-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_045
-- name    : RealPinwheel_FiveSixths_WitnessD7_045
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:53:57.336044+00:00
-- url     : https://prove2.me/theorems/887f2a16-3010-49c7-973f-d092fc08ae22
-- title:
--   Exact witness block D7_045
-- statement:
--   These exact witnesses represent words 675 through 699 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 675–699; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_045_674 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_674
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 31 (.leaf (-13)) (.leaf (-17)))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.branch 39 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_045_675 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (6)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_675
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 34 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 37 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.branch 34 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-21)))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-21)) (.leaf (-19))) (.branch 33 (.leaf (-17)) (.branch 34 (.leaf (-15)) (.leaf (-13))))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-9))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 25 (.branch 11 (.leaf (-7)) (.leaf (-6))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (-1))]
def witnessD7_045_676 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (2))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_676
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 33 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0))]
def witnessD7_045_677 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_677
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-19)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (-7)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-5)),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 37 (.branch 35 (.leaf (-13)) (.branch 36 (.leaf (-11)) (.leaf (-9)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-7))) (.branch 39 (.leaf (-5)) (.leaf (-3)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_045_678 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (2)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_678
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 20 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 39 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.leaf (-30)) (.branch 12 (.leaf (-29)) (.leaf (-28)))) (.branch 15 (.branch 14 (.leaf (-27)) (.leaf (-26))) (.branch 16 (.leaf (-25)) (.leaf (-24))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 23 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.leaf (-16)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_045_679 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_679
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.branch 11 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-26))),
  (.branch 34 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 22 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 34 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7))))),
  (.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 20 (.branch 17 (.branch 15 (.leaf (-26)) (.branch 16 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-21))))) (.branch 23 (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18)))) (.branch 25 (.branch 24 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_045_680 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_680
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_045_681 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_681
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_045_682 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_682
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_045_683 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (2)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_683
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-8)) (.branch 38 (.leaf (-9)) (.leaf (-12))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-12)) (.leaf (-10))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_045_684 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_684
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-25)) (.branch 17 (.leaf (-24)) (.leaf (-23)))) (.branch 19 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20))))) (.branch 24 (.branch 22 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_045_685 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (2)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (2)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (5)) (.branch 39 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_685
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-5)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 29 (.leaf (-5)) (.branch 30 (.leaf (-4)) (.leaf (-3)))) (.branch 32 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 37 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 39 (.leaf (-4)) (.leaf (-3))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_045_686 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (4))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_686
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 27 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_045_687 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (6))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_687
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-19))) (.branch 33 (.leaf (-20)) (.leaf (-21)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-18)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_045_688 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (2)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (0))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_688
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 17 (.leaf (-14)) (.branch 37 (.leaf (-17)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 32 (.leaf (-8)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-14)) (.leaf (-9)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 38 (.branch 37 (.leaf (-6)) (.leaf (-5))) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_045_689 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (6))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_689
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 21 (.leaf (7)) (.leaf (8))) (.branch 27 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-15)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-6)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 36 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 37 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_045_690 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (5))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (4)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (3))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_690
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-8)) (.leaf (-10)))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_045_691 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (3))) (.branch 28 (.leaf (5)) (.branch 29 (.leaf (4)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (2))) (.branch 38 (.leaf (6)) (.branch 39 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_691
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-26))) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 25 (.leaf (-32)) (.branch 31 (.leaf (-30)) (.leaf (-28)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-14)) (.leaf (-7))))),
  (.branch 38 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 28 (.branch 5 (.leaf (-12)) (.leaf (-11))) (.branch 34 (.leaf (-9)) (.leaf (-7)))),
  (.branch 35 (.leaf (-2)) (.leaf (0))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_045_692 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (0))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_692
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 32 (.branch 5 (.leaf (-28)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 25 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 29 (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_045_693 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (3))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_693
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 33 (.leaf (-9)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (-1))]
def witnessD7_045_694 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_694
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 37 (.leaf (0)) (.leaf (-3))),
  (.branch 17 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 32 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_045_695 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (6))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_695
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 22 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-8)) (.leaf (-10)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-28))) (.branch 30 (.leaf (-29)) (.leaf (-30)))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0))]
def witnessD7_045_696 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_696
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-32)) (.leaf (-31))) (.branch 11 (.leaf (-30)) (.leaf (-29)))) (.branch 14 (.branch 13 (.leaf (-28)) (.leaf (-27))) (.branch 15 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-24)) (.leaf (-23))) (.branch 19 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.leaf (-17)))))) (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_045_697 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (5))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (3)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (2)) (.leaf (5))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (2))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_697
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 31 (.leaf (-22)) (.leaf (-23)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (-5)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 32 (.leaf (-23)) (.leaf (-21))) (.branch 39 (.leaf (-14)) (.leaf (-7)))),
  (.branch 12 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (0)))),
  (.branch 37 (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-9)),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_045_698 : CycleWitness 7 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_698
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (-4)) (.leaf (-6)))),
  (.branch 16 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.leaf (-8)) (.branch 39 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-6)) (.leaf (-5))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 17 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-22)))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_045 : Fin 25 → CycleWitness 7 := ![witnessD7_045_674, witnessD7_045_675, witnessD7_045_676, witnessD7_045_677, witnessD7_045_678, witnessD7_045_679, witnessD7_045_680, witnessD7_045_681, witnessD7_045_682, witnessD7_045_683, witnessD7_045_684, witnessD7_045_685, witnessD7_045_686, witnessD7_045_687, witnessD7_045_688, witnessD7_045_689, witnessD7_045_690, witnessD7_045_691, witnessD7_045_692, witnessD7_045_693, witnessD7_045_694, witnessD7_045_695, witnessD7_045_696, witnessD7_045_697, witnessD7_045_698]
end RealPinwheel.FiveSixths


