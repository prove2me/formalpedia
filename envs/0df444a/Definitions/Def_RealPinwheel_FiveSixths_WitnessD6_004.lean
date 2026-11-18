-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_004
-- name    : RealPinwheel_FiveSixths_WitnessD6_004
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:11:31.195229+00:00
-- url     : https://prove2.me/theorems/29013fd8-9005-4ba9-bb89-cb498ba1b8a5
-- title:
--   Exact witness block D6_004
-- statement:
--   These exact witnesses represent words 80 through 105 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 80–105; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_004_79 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (4)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_79
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 22 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 22 (.leaf (-16)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-28)) (.leaf (-29)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (-7))) (.branch 37 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 31 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-13)))),
  (.leaf (-1)),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8)))) (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 35 (.branch 32 (.branch 18 (.leaf (-29)) (.leaf (-27))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-21)) (.leaf (-18))))) (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-6)) (.leaf (-3))))]
def witnessD6_004_80 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1)))))) (.branch 30 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_80
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (10)) (.leaf (11)))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14)))) (.branch 26 (.leaf (15)) (.branch 27 (.leaf (16)) (.leaf (17))))) (.branch 34 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 37 (.branch 36 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))))),
  (.branch 20 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-22))),
  (.branch 38 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 23 (.branch 20 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-20)) (.branch 22 (.leaf (-19)) (.leaf (-18))))) (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.leaf (-14)) (.branch 28 (.leaf (-13)) (.leaf (-12)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_004_81 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_81
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 39 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-20))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16))))) (.branch 27 (.branch 26 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6))))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_004_82 : CycleWitness 6 where
  length := 40
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_82
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 33 (.branch 31 (.leaf (12)) (.leaf (13))) (.branch 36 (.leaf (14)) (.branch 38 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-4)) (.leaf (-2))),
  (.branch 36 (.leaf (-5)) (.leaf (-3))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 22 (.branch 19 (.branch 18 (.leaf (-23)) (.leaf (-22))) (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-20)) (.leaf (-19))))) (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))))) (.branch 34 (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))) (.branch 37 (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-3)) (.branch 39 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_004_83 : CycleWitness 6 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (2))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_83
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.leaf (15)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-6)) (.branch 30 (.leaf (-8)) (.leaf (-10))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-32))),
  (.branch 20 (.leaf (0)) (.leaf (-19))),
  (.branch 33 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 38 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.leaf (-10)) (.branch 35 (.leaf (-9)) (.leaf (-8)))),
  (.branch 27 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-32)) (.leaf (-31))) (.branch 10 (.leaf (-30)) (.leaf (-29)))) (.branch 13 (.branch 12 (.leaf (-28)) (.leaf (-27))) (.branch 14 (.leaf (-26)) (.leaf (-25))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-24)) (.leaf (-23))) (.branch 18 (.leaf (-22)) (.leaf (-21)))) (.branch 21 (.branch 20 (.leaf (-20)) (.leaf (-19))) (.branch 22 (.leaf (-18)) (.leaf (-17)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 30 (.leaf (-10)) (.leaf (-9))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-19)) (.leaf (-18))) (.branch 23 (.leaf (-17)) (.leaf (-16)))) (.branch 26 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 27 (.leaf (-13)) (.branch 28 (.leaf (-12)) (.leaf (-11)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6))))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_004_84 : CycleWitness 6 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (5))))))))
  code := certificateD6_84
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.branch 11 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.branch 12 (.leaf (-3)) (.leaf (-4))))),
  (.branch 13 (.leaf (0)) (.leaf (-26))),
  (.branch 26 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 38 (.leaf (-8)) (.leaf (-4))),
  (.leaf (-4)),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-26)) (.branch 15 (.leaf (-25)) (.leaf (-24)))) (.branch 17 (.leaf (-23)) (.branch 18 (.leaf (-22)) (.leaf (-21))))) (.branch 22 (.branch 20 (.leaf (-20)) (.branch 21 (.leaf (-19)) (.leaf (-18)))) (.branch 24 (.branch 23 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-15)) (.leaf (-14)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-13)) (.branch 28 (.leaf (-12)) (.leaf (-11)))) (.branch 30 (.leaf (-10)) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-13)) (.branch 28 (.leaf (-12)) (.leaf (-11)))) (.branch 30 (.leaf (-10)) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_004_85 : CycleWitness 6 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (4)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (0)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (5)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_85
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-18)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.branch 17 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 33 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))))),
  (.leaf (-2)),
  (.branch 36 (.branch 16 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-13)) (.leaf (-8))))),
  (.branch 34 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 28 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_004_86 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 6 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (4))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.leaf (2)))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_86
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 16 (.leaf (9)) (.leaf (10)))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (11)) (.branch 21 (.leaf (12)) (.leaf (13)))) (.branch 24 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16))))) (.branch 33 (.branch 30 (.leaf (17)) (.branch 31 (.leaf (18)) (.leaf (19)))) (.branch 35 (.leaf (20)) (.branch 37 (.leaf (21)) (.leaf (22))))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 3 (.leaf (-14)) (.branch 22 (.leaf (-21)) (.leaf (-26))))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 34 (.leaf (-23)) (.branch 36 (.leaf (-21)) (.leaf (-19))))),
  (.branch 30 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_004_87 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_87
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 27 (.branch 21 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.branch 25 (.leaf (13)) (.leaf (14))))) (.branch 33 (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17)))) (.branch 35 (.leaf (18)) (.branch 37 (.leaf (19)) (.leaf (20))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-9)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.branch 24 (.branch 22 (.leaf (-18)) (.leaf (-17))) (.branch 26 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 30 (.leaf (-14)) (.leaf (-13))) (.branch 34 (.leaf (-12)) (.branch 36 (.leaf (-11)) (.leaf (-10)))))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.branch 12 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_004_88 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (1))))))))
  code := certificateD6_88
  counts := ![(.branch 18 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))) (.branch 27 (.branch 21 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.branch 25 (.leaf (13)) (.leaf (14))))) (.branch 33 (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17)))) (.branch 35 (.leaf (18)) (.branch 37 (.leaf (19)) (.leaf (20))))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (-3)) (.leaf (-5)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-23))),
  (.branch 34 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.branch 24 (.branch 22 (.leaf (-18)) (.leaf (-17))) (.branch 26 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 30 (.leaf (-14)) (.leaf (-13))) (.branch 34 (.leaf (-12)) (.branch 36 (.leaf (-11)) (.leaf (-10)))))),
  (.branch 33 (.branch 31 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-3)))) (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0))))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_004_89 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_89
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-13)) (.branch 24 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-25))),
  (.branch 32 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 31 (.branch 25 (.leaf (-20)) (.branch 28 (.leaf (-19)) (.leaf (-18)))) (.branch 34 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-11))))),
  (.branch 35 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 14 (.leaf (-25)) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20))))) (.branch 22 (.branch 20 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-17)))) (.branch 23 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_004_90 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_90
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 13 (.branch 10 (.leaf (-15)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 11 (.leaf (-7)) (.branch 30 (.leaf (-9)) (.leaf (-10))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 36 (.leaf (-18)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.leaf (-10)) (.leaf (-7))),
  (.branch 37 (.leaf (-4)) (.leaf (-2))),
  (.branch 35 (.branch 23 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0))))]
def witnessD6_004_91 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (5))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD6_91
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 32 (.leaf (9)) (.branch 36 (.leaf (10)) (.leaf (11)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 21 (.leaf (-10)) (.branch 24 (.leaf (-14)) (.leaf (-16))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 23 (.leaf (-27)) (.leaf (-29)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.branch 37 (.leaf (-13)) (.leaf (-10))))),
  (.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.branch 31 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_004_92 : CycleWitness 6 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3))))))))
  code := certificateD6_92
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 29 (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 32 (.leaf (-2)) (.leaf (0))),
  (.branch 33 (.branch 30 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))]
def witnessD6_004_93 : CycleWitness 6 where
  length := 37
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1))))))))
  code := certificateD6_93
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-18)) (.leaf (-21)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 28 (.branch 22 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19)))) (.branch 31 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16))))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0))))),
  (.branch 29 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 36 (.leaf (-11)) (.leaf (-6)))),
  (.branch 35 (.branch 16 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 8 (.leaf (-16)) (.branch 33 (.leaf (-15)) (.leaf (-12)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.leaf (-2)))))]
def witnessD6_004_94 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (5))))) (.branch 27 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_94
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (6))))) (.branch 12 (.branch 10 (.leaf (7)) (.branch 11 (.leaf (8)) (.leaf (9)))) (.branch 15 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 16 (.leaf (12)) (.leaf (13)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (14)) (.branch 20 (.leaf (15)) (.leaf (16)))) (.branch 24 (.branch 22 (.leaf (17)) (.leaf (18))) (.branch 25 (.leaf (19)) (.leaf (20))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (21)) (.leaf (22))) (.branch 30 (.leaf (23)) (.leaf (24)))) (.branch 34 (.branch 33 (.leaf (25)) (.leaf (26))) (.branch 35 (.leaf (27)) (.leaf (28))))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.branch 4 (.leaf (-6)) (.leaf (-8))))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 32 (.leaf (-8)) (.leaf (-7))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_004_95 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 27 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 35 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_95
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (6))))) (.branch 12 (.branch 10 (.leaf (7)) (.branch 11 (.leaf (8)) (.leaf (9)))) (.branch 15 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 16 (.leaf (12)) (.leaf (13)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (14)) (.branch 20 (.leaf (15)) (.leaf (16)))) (.branch 24 (.branch 22 (.leaf (17)) (.leaf (18))) (.branch 25 (.leaf (19)) (.leaf (20))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (21)) (.leaf (22))) (.branch 30 (.leaf (23)) (.leaf (24)))) (.branch 34 (.branch 33 (.leaf (25)) (.leaf (26))) (.branch 35 (.leaf (27)) (.leaf (28))))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.branch 4 (.leaf (-6)) (.leaf (-8))))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.leaf (-8)) (.leaf (-7))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_004_96 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1)))))) (.branch 27 (.branch 24 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_96
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.leaf (9)) (.branch 15 (.leaf (10)) (.leaf (11)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 23 (.leaf (15)) (.branch 24 (.leaf (16)) (.leaf (17))))) (.branch 30 (.branch 28 (.leaf (18)) (.branch 29 (.leaf (19)) (.leaf (20)))) (.branch 33 (.branch 32 (.leaf (21)) (.leaf (22))) (.branch 35 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11))),
  (.branch 34 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_004_97 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 6 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 15 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2)))))) (.branch 27 (.branch 24 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_97
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.leaf (9)) (.branch 15 (.leaf (10)) (.leaf (11)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 23 (.leaf (15)) (.branch 24 (.leaf (16)) (.leaf (17))))) (.branch 30 (.branch 28 (.leaf (18)) (.branch 29 (.leaf (19)) (.leaf (20)))) (.branch 33 (.branch 32 (.leaf (21)) (.leaf (22))) (.branch 35 (.leaf (23)) (.leaf (24))))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_004_98 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 10 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 11 (.leaf (4)) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (0)) (.leaf (2)))))) (.branch 28 (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_98
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 8 (.leaf (5)) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 15 (.leaf (9)) (.leaf (10)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (11)) (.branch 20 (.leaf (12)) (.leaf (13)))) (.branch 23 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))) (.branch 32 (.branch 28 (.leaf (17)) (.branch 30 (.leaf (18)) (.leaf (19)))) (.branch 33 (.leaf (20)) (.branch 35 (.leaf (21)) (.leaf (22))))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.branch 21 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 27 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_004_99 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 14 (.branch 11 (.leaf (0)) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))))) (.branch 27 (.branch 23 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_99
  counts := ![(.branch 17 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.leaf (9)) (.branch 16 (.leaf (10)) (.leaf (11)))))) (.branch 26 (.branch 22 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 23 (.leaf (15)) (.branch 25 (.leaf (16)) (.leaf (17))))) (.branch 31 (.branch 28 (.leaf (18)) (.branch 29 (.leaf (19)) (.leaf (20)))) (.branch 34 (.branch 32 (.leaf (21)) (.leaf (22))) (.branch 35 (.leaf (23)) (.leaf (24))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_004_100 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (0)) (.leaf (1)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (1)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_100
  counts := ![(.branch 17 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.branch 24 (.leaf (13)) (.leaf (14))))) (.branch 31 (.branch 28 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17)))) (.branch 33 (.leaf (18)) (.branch 35 (.leaf (19)) (.leaf (20))))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11))),
  (.branch 34 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 32 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_004_101 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (4)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_101
  counts := ![(.branch 17 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.branch 24 (.leaf (13)) (.leaf (14))))) (.branch 31 (.branch 28 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17)))) (.branch 33 (.leaf (18)) (.branch 35 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 35 (.leaf (-4)) (.leaf (-2))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_004_102 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_102
  counts := ![(.branch 17 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 24 (.leaf (12)) (.leaf (13))))) (.branch 31 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 33 (.leaf (16)) (.branch 35 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.leaf (-4)) (.leaf (-2))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_004_103 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_103
  counts := ![(.branch 17 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 24 (.leaf (12)) (.leaf (13))))) (.branch 30 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 32 (.leaf (16)) (.branch 35 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-23))),
  (.branch 31 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_004_104 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_104
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 22 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 30 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 32 (.leaf (-7)) (.leaf (-5))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_004 : Fin 26 → CycleWitness 6 := ![witnessD6_004_79, witnessD6_004_80, witnessD6_004_81, witnessD6_004_82, witnessD6_004_83, witnessD6_004_84, witnessD6_004_85, witnessD6_004_86, witnessD6_004_87, witnessD6_004_88, witnessD6_004_89, witnessD6_004_90, witnessD6_004_91, witnessD6_004_92, witnessD6_004_93, witnessD6_004_94, witnessD6_004_95, witnessD6_004_96, witnessD6_004_97, witnessD6_004_98, witnessD6_004_99, witnessD6_004_100, witnessD6_004_101, witnessD6_004_102, witnessD6_004_103, witnessD6_004_104]
end RealPinwheel.FiveSixths


