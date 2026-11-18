-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_052
-- name    : RealPinwheel_FiveSixths_WitnessD7_052
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:18.3705+00:00
-- url     : https://prove2.me/theorems/64f36105-7a4f-456d-8b46-4856392dfc59
-- title:
--   Exact witness block D7_052
-- statement:
--   These exact witnesses represent words 858 through 884 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 858–884; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_052_857 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (6))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_857
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 16 (.leaf (-14)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 17 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-14)))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 20 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.leaf (-5)))),
  (.branch 29 (.leaf (-4)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_052_858 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_858
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))) (.branch 28 (.branch 14 (.leaf (-5)) (.leaf (-6))) (.branch 32 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.leaf (0)) (.leaf (-19))),
  (.branch 35 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 30 (.leaf (-7)) (.leaf (-5))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_052_859 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (5)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_859
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-21)) (.leaf (-22)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 31 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.branch 11 (.leaf (-22)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-3)) (.leaf (0))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_052_860 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (4)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_860
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.branch 31 (.leaf (-19)) (.leaf (-21))))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-9)))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 34 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-17))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 14 (.leaf (-6)) (.leaf (-5))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 35 (.leaf (-7)) (.leaf (-5)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_861 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (6)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (6)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_861
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))) (.branch 24 (.leaf (-5)) (.branch 33 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-5)))),
  (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.branch 4 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-3)) (.leaf (0))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_862 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (5))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (6))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_862
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 17 (.leaf (-22)) (.branch 24 (.leaf (-23)) (.leaf (-24))))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 29 (.leaf (-9)) (.leaf (-11)))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 25 (.leaf (-24)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 32 (.branch 30 (.leaf (-11)) (.branch 31 (.leaf (-10)) (.leaf (-9)))) (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_052_863 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_863
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-19)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-11)) (.branch 32 (.leaf (-13)) (.leaf (-14))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 35 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 16 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 34 (.branch 18 (.leaf (-19)) (.leaf (-17))) (.branch 35 (.leaf (-12)) (.leaf (-7)))),
  (.branch 34 (.branch 33 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-8)))),
  (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_864 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (6)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_864
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 26 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 30 (.leaf (-13)) (.branch 33 (.leaf (-10)) (.leaf (-7)))),
  (.branch 21 (.leaf (-5)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-28)) (.branch 10 (.leaf (-27)) (.leaf (-26)))) (.branch 13 (.branch 12 (.leaf (-25)) (.leaf (-24))) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_865 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_865
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 31 (.leaf (-12)) (.leaf (-13)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-4)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 27 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 32 (.leaf (-13)) (.leaf (-11))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-7)) (.leaf (-5))))),
  (.branch 28 (.leaf (-6)) (.leaf (-5))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_052_866 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (4))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_866
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 19 (.leaf (-6)) (.branch 24 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-8)) (.leaf (-7))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 22 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_052_867 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_867
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 19 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_868 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (5)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_868
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-4)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 22 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_869 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (3)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_869
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-8)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-21)) (.leaf (-22)))) (.branch 24 (.leaf (-23)) (.branch 31 (.leaf (-24)) (.leaf (-25))))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 23 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-5)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-7)) (.leaf (-5))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_870 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (2))))))))
  code := certificateD7_870
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 14 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-6)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.branch 22 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_871 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (4)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (3)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (5)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_871
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 32 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-22)) (.leaf (-23)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))) (.branch 20 (.leaf (-3)) (.branch 25 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-13))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 34 (.branch 8 (.leaf (-23)) (.leaf (-21))) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 26 (.leaf (-5)) (.leaf (0))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_872 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_872
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-7)),
  (.leaf (0)),
  (.branch 33 (.branch 22 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_873 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_873
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 18 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 19 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 28 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_874 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (6)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_874
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 11 (.leaf (-11)) (.branch 32 (.leaf (-15)) (.leaf (-16))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-6)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-13))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 30 (.leaf (-9)) (.leaf (-7))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 22 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_875 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (3)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (6))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_875
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-29)) (.leaf (-30)))) (.branch 21 (.branch 16 (.leaf (-31)) (.leaf (-32))) (.branch 26 (.leaf (-33)) (.leaf (-34))))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 33 (.branch 27 (.leaf (-34)) (.leaf (-28))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-14)) (.leaf (-7))))),
  (.branch 34 (.branch 3 (.leaf (-22)) (.leaf (-21))) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.leaf (-10)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_052_876 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (6)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_876
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 31 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_052_877 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (1)) (.leaf (5)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (2)) (.leaf (6)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_877
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-16)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-16)))) (.branch 16 (.leaf (-18)) (.branch 20 (.leaf (-20)) (.leaf (-25))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 35 (.leaf (-2)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 27 (.leaf (-12)) (.leaf (-17)))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-10)) (.leaf (-7))))),
  (.branch 33 (.branch 21 (.leaf (-25)) (.branch 27 (.leaf (-24)) (.leaf (-23)))) (.branch 34 (.leaf (-20)) (.branch 35 (.leaf (-17)) (.leaf (-14))))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.leaf (-5)),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 30 (.leaf (-15)) (.leaf (-14)))) (.branch 33 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_052_878 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_878
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 12 (.leaf (-23)) (.leaf (-24)))) (.branch 27 (.branch 22 (.leaf (-25)) (.leaf (-26))) (.branch 32 (.leaf (-27)) (.leaf (-28))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 29 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 29 (.branch 24 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-2)) (.leaf (0))))),
  (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-21))) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.leaf (-10)) (.leaf (-7))),
  (.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_052_879 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_879
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 12 (.leaf (-23)) (.leaf (-24)))) (.branch 27 (.branch 22 (.leaf (-25)) (.leaf (-26))) (.branch 32 (.leaf (-27)) (.leaf (-28))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 29 (.branch 24 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-2)) (.leaf (0))))),
  (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-21))) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.leaf (-10)) (.leaf (-7))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_052_880 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (5)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (6))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (5)) (.leaf (4))))))))
  code := certificateD7_880
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-25)) (.leaf (-26)))) (.branch 21 (.branch 16 (.leaf (-27)) (.leaf (-28))) (.branch 31 (.leaf (-29)) (.leaf (-31))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-13)) (.leaf (-15)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-9)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-18)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 33 (.branch 32 (.leaf (-31)) (.leaf (-25))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-13)) (.leaf (-7))))),
  (.branch 14 (.leaf (-15)) (.branch 35 (.leaf (-13)) (.leaf (-7)))),
  (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))),
  (.branch 33 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 29 (.leaf (-4)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_052_881 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (6)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_881
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-6)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-23))),
  (.branch 31 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 31 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-9)) (.leaf (-8))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_052_882 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (5)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_882
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-15)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 31 (.leaf (-14)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-10)) (.leaf (-7))))),
  (.leaf (-1)),
  (.branch 34 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-14))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 29 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_052_883 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (2)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (5))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (2))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_883
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 17 (.leaf (-22)) (.branch 24 (.leaf (-23)) (.leaf (-24))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 34 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 25 (.leaf (-24)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 13 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_052 : Fin 27 → CycleWitness 7 := ![witnessD7_052_857, witnessD7_052_858, witnessD7_052_859, witnessD7_052_860, witnessD7_052_861, witnessD7_052_862, witnessD7_052_863, witnessD7_052_864, witnessD7_052_865, witnessD7_052_866, witnessD7_052_867, witnessD7_052_868, witnessD7_052_869, witnessD7_052_870, witnessD7_052_871, witnessD7_052_872, witnessD7_052_873, witnessD7_052_874, witnessD7_052_875, witnessD7_052_876, witnessD7_052_877, witnessD7_052_878, witnessD7_052_879, witnessD7_052_880, witnessD7_052_881, witnessD7_052_882, witnessD7_052_883]
end RealPinwheel.FiveSixths


