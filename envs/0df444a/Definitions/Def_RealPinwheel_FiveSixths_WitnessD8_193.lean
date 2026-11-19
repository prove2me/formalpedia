-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_193
-- name    : RealPinwheel_FiveSixths_WitnessD8_193
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:39:01.897484+00:00
-- url     : https://prove2.me/theorems/88de9c91-729a-4805-bfef-e86170a1bcbf
-- title:
--   Exact witness block D8_193
-- statement:
--   These exact witnesses represent words 2075 through 2096 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2075–2096; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_193_2074 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (7)) (.branch 21 (.leaf (1)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (7)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_2074
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 44 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-35)) (.leaf (-36)))),
  (.branch 12 (.leaf (0)) (.leaf (-21))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-36)) (.leaf (-34))) (.branch 30 (.leaf (-32)) (.leaf (-30)))) (.branch 33 (.branch 32 (.leaf (-28)) (.leaf (-26))) (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-22)) (.leaf (-20)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-16))) (.branch 39 (.leaf (-14)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 39 (.branch 36 (.branch 13 (.leaf (-21)) (.leaf (-20))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-16)) (.leaf (-14))))) (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-8)))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_193_2075 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (7))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (2)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (3))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (7)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (4)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_2075
  counts := ![(.branch 22 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 29 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 41 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.leaf (15)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 33 (.leaf (-11)) (.branch 41 (.leaf (-10)) (.leaf (-8)))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_193_2076 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2076
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 44 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-35))),
  (.branch 25 (.leaf (0)) (.leaf (-20))),
  (.branch 40 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-35)) (.leaf (-34))) (.branch 13 (.leaf (-33)) (.leaf (-32)))) (.branch 16 (.branch 15 (.leaf (-31)) (.leaf (-30))) (.branch 17 (.leaf (-29)) (.leaf (-28))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-27)) (.leaf (-26))) (.branch 21 (.leaf (-25)) (.leaf (-24)))) (.branch 24 (.branch 23 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.branch 26 (.leaf (-20)) (.leaf (-19))))))) (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-18)) (.leaf (-17))) (.branch 30 (.leaf (-16)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.branch 29 (.leaf (-17)) (.leaf (-16))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_193_2077 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (1)) (.leaf (5)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (7)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (1)) (.leaf (7)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (6)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (0))))) (.branch 42 (.branch 40 (.leaf (4)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_2077
  counts := ![(.branch 19 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-20)) (.leaf (-30)))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))) (.branch 29 (.leaf (-15)) (.branch 37 (.leaf (-17)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.branch 20 (.branch 16 (.leaf (-30)) (.leaf (-29))) (.branch 24 (.leaf (-28)) (.leaf (-27)))) (.branch 36 (.branch 32 (.leaf (-26)) (.leaf (-25))) (.branch 40 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-16)))))),
  (.branch 43 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-18)) (.leaf (-14)))),
  (.branch 42 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4))))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-1)) (.leaf (0)))]
def witnessD8_193_2078 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (7)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (6)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (7)) (.branch 26 (.leaf (4)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0))))) (.branch 42 (.branch 40 (.leaf (7)) (.branch 41 (.leaf (3)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_2078
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 36 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_193_2079 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (6)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (4)) (.leaf (2))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (1))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2079
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-3)) (.branch 39 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (-29)) (.leaf (-30)))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-5)) (.leaf (-4))),
  (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-30)) (.branch 32 (.leaf (-28)) (.leaf (-26)))) (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-22))) (.branch 36 (.leaf (-20)) (.leaf (-18))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-16)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.branch 39 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_193_2080 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (4)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (7))))) (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2080
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-36))),
  (.branch 24 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 37 (.branch 33 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-36)) (.leaf (-35))) (.branch 12 (.leaf (-34)) (.leaf (-33)))) (.branch 15 (.branch 14 (.leaf (-32)) (.leaf (-31))) (.branch 16 (.leaf (-30)) (.branch 17 (.leaf (-29)) (.leaf (-28)))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-27)) (.leaf (-26))) (.branch 21 (.leaf (-25)) (.leaf (-24)))) (.branch 24 (.branch 23 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.branch 26 (.leaf (-20)) (.leaf (-19))))))) (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-18)) (.leaf (-17))) (.branch 30 (.leaf (-16)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-19)) (.branch 28 (.leaf (-18)) (.leaf (-17))))) (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 32 (.leaf (-14)) (.branch 33 (.leaf (-13)) (.leaf (-12)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_193_2081 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (7)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (5)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (6)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (7)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (6)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (7)))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_2081
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-29))) (.branch 18 (.leaf (-34)) (.leaf (-36)))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-33))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.branch 19 (.leaf (-36)) (.branch 36 (.leaf (-35)) (.leaf (-32)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-16)) (.leaf (-8))))),
  (.branch 34 (.leaf (-6)) (.branch 40 (.leaf (-3)) (.leaf (0)))),
  (.branch 40 (.branch 38 (.branch 4 (.leaf (-33)) (.leaf (-32))) (.branch 39 (.leaf (-28)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-16))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 21 (.leaf (-10)) (.branch 44 (.leaf (-8)) (.leaf (-4)))),
  (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_193_2082 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (0))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (5)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (6)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (7)) (.leaf (3)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (6)) (.leaf (7))))))))
  code := certificateD8_2082
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.leaf (15)))))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-25))) (.branch 36 (.leaf (-26)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-19)) (.leaf (-21)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-10)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-25))) (.branch 39 (.leaf (-22)) (.leaf (-19)))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-13))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-7)) (.leaf (-4)))))),
  (.branch 41 (.branch 28 (.leaf (-21)) (.branch 40 (.leaf (-19)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-13)) (.leaf (-10))) (.branch 44 (.leaf (-7)) (.leaf (-4))))),
  (.branch 42 (.branch 19 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-7)) (.leaf (-4))))),
  (.branch 10 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (0))]
def witnessD8_193_2083 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (6)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (3)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0))))) (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (7)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_2083
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 44 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-34))),
  (.branch 26 (.leaf (0)) (.leaf (-19))),
  (.branch 41 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 36 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0))))),
  (.branch 28 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-34)) (.leaf (-33))) (.branch 14 (.leaf (-32)) (.leaf (-31)))) (.branch 17 (.branch 16 (.leaf (-30)) (.leaf (-29))) (.branch 18 (.leaf (-28)) (.leaf (-27))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-26)) (.leaf (-25))) (.branch 22 (.leaf (-24)) (.leaf (-23)))) (.branch 25 (.branch 24 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-20)) (.branch 27 (.leaf (-19)) (.leaf (-18))))))) (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-17)) (.leaf (-16))) (.branch 31 (.leaf (-15)) (.leaf (-14)))) (.branch 34 (.branch 33 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-11)) (.leaf (-10))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_193_2084 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (6)) (.leaf (1)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (7)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (7)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (5)))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (1)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_2084
  counts := ![(.branch 20 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 40 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_193_2085 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (7)) (.leaf (1)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (6)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (5)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (7)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2085
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))) (.branch 27 (.leaf (-7)) (.branch 36 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 22 (.leaf (-17)) (.branch 28 (.leaf (-20)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 25 (.leaf (-2)) (.branch 34 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-21)) (.leaf (-22)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))),
  (.branch 38 (.branch 3 (.leaf (-19)) (.leaf (-18))) (.branch 44 (.leaf (-17)) (.leaf (-12)))),
  (.branch 36 (.branch 29 (.leaf (-23)) (.leaf (-22))) (.branch 43 (.leaf (-21)) (.branch 44 (.leaf (-17)) (.leaf (-13))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-8)) (.leaf (-7))),
  (.branch 42 (.branch 18 (.leaf (-22)) (.branch 41 (.leaf (-20)) (.leaf (-16)))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 41 (.branch 39 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_193_2086 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (7)) (.leaf (1)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (6))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (7))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (1)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1)))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2086
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 36 (.leaf (-15)) (.leaf (-17)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-15))) (.branch 17 (.leaf (-18)) (.leaf (-25)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 35 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))),
  (.branch 23 (.leaf (0)) (.branch 32 (.leaf (-4)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 39 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.leaf (-8)))),
  (.branch 43 (.branch 37 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-12)) (.leaf (-8)))),
  (.branch 34 (.branch 18 (.leaf (-25)) (.branch 26 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.branch 42 (.leaf (-22)) (.leaf (-18))) (.branch 44 (.leaf (-14)) (.leaf (-10))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 41 (.branch 17 (.leaf (-14)) (.branch 29 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-8))) (.branch 44 (.leaf (-6)) (.leaf (-4))))),
  (.branch 35 (.branch 33 (.leaf (-11)) (.branch 34 (.leaf (-9)) (.leaf (-7)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-3))) (.branch 38 (.leaf (-1)) (.leaf (0))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_193_2087 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (6)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (7))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (5)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2087
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 23 (.leaf (-12)) (.branch 36 (.leaf (-15)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-23)) (.leaf (-28)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 22 (.leaf (-9)) (.branch 35 (.leaf (-14)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.branch 34 (.leaf (-3)) (.leaf (-8))))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-28)))),
  (.branch 8 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 42 (.branch 37 (.leaf (-18)) (.leaf (-17))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-11)) (.leaf (-8))))),
  (.branch 26 (.branch 14 (.branch 8 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25)))) (.branch 38 (.branch 32 (.leaf (-24)) (.leaf (-23))) (.branch 44 (.leaf (-22)) (.leaf (-16))))),
  (.branch 43 (.branch 36 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-11)) (.leaf (-8)))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-8)) (.leaf (-7))),
  (.branch 40 (.branch 27 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-23)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-17))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-11)) (.leaf (-8)))))),
  (.branch 41 (.branch 9 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-9))) (.branch 44 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (0))]
def witnessD8_193_2088 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (3)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (7)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (6)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (5)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (3)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (4)) (.branch 44 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2088
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-29)) (.leaf (-34)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-37)) (.leaf (-38)))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (-15)) (.leaf (-16))))]
  high := ![(.branch 43 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-8)) (.leaf (-4)))),
  (.branch 42 (.branch 8 (.leaf (-34)) (.branch 25 (.leaf (-33)) (.leaf (-32)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-16)) (.leaf (-8))))),
  (.branch 23 (.leaf (-4)) (.branch 40 (.leaf (-3)) (.leaf (0)))),
  (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-1)),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-38)) (.leaf (-36))) (.branch 29 (.leaf (-34)) (.leaf (-32)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-28))) (.branch 33 (.leaf (-26)) (.branch 34 (.leaf (-24)) (.leaf (-22)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-18))) (.branch 38 (.leaf (-16)) (.branch 39 (.leaf (-14)) (.leaf (-12))))) (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-16)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_193_2089 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (7)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (6)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (7)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (5))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (6))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (6)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2089
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-33))) (.branch 25 (.leaf (-34)) (.leaf (-35)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-17))) (.branch 29 (.leaf (-18)) (.branch 40 (.leaf (-19)) (.leaf (-20))))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 38 (.branch 26 (.leaf (-35)) (.leaf (-32))) (.branch 39 (.leaf (-28)) (.leaf (-24)))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-16))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-16))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 11 (.leaf (-5)) (.leaf (-4))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_193_2090 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (6)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (7)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_2090
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 45 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-34))),
  (.branch 26 (.leaf (0)) (.leaf (-19))),
  (.branch 41 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 37 (.branch 33 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.leaf (-5)) (.leaf (-4))),
  (.branch 39 (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-34)) (.leaf (-33))) (.branch 14 (.leaf (-32)) (.leaf (-31)))) (.branch 17 (.branch 16 (.leaf (-30)) (.leaf (-29))) (.branch 18 (.leaf (-28)) (.leaf (-27))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-26)) (.leaf (-25))) (.branch 22 (.leaf (-24)) (.leaf (-23)))) (.branch 25 (.branch 24 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-20)) (.branch 27 (.leaf (-19)) (.leaf (-18))))))) (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-17)) (.leaf (-16))) (.branch 31 (.leaf (-15)) (.leaf (-14)))) (.branch 34 (.branch 33 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-11)) (.leaf (-10))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_193_2091 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (4)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (7)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2091
  counts := ![(.branch 20 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 44 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-39))),
  (.branch 21 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 44 (.leaf (-5)) (.leaf (-4))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 42 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-39)) (.leaf (-38))) (.branch 9 (.leaf (-37)) (.leaf (-36)))) (.branch 12 (.branch 11 (.leaf (-35)) (.leaf (-34))) (.branch 13 (.leaf (-33)) (.branch 14 (.leaf (-32)) (.leaf (-31)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-30)) (.leaf (-29))) (.branch 18 (.leaf (-28)) (.branch 19 (.leaf (-27)) (.leaf (-26))))) (.branch 22 (.branch 21 (.leaf (-25)) (.leaf (-24))) (.branch 23 (.leaf (-23)) (.branch 24 (.leaf (-22)) (.leaf (-21))))))) (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.branch 29 (.leaf (-17)) (.leaf (-16))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 27 (.branch 24 (.branch 22 (.leaf (-24)) (.branch 23 (.leaf (-23)) (.leaf (-22)))) (.branch 25 (.leaf (-21)) (.branch 26 (.leaf (-20)) (.leaf (-19))))) (.branch 30 (.branch 28 (.leaf (-18)) (.branch 29 (.leaf (-17)) (.leaf (-16)))) (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_193_2092 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (4)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (6)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (7))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5))))) (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (7)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_2092
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 33 (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13))))) (.branch 38 (.branch 35 (.leaf (14)) (.leaf (15))) (.branch 41 (.leaf (16)) (.branch 43 (.leaf (17)) (.leaf (18))))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-37))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-21)) (.leaf (-22)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-6)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 37 (.branch 3 (.leaf (-37)) (.leaf (-36))) (.branch 38 (.leaf (-32)) (.branch 39 (.leaf (-28)) (.leaf (-24))))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-16))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 42 (.branch 18 (.leaf (-22)) (.branch 41 (.leaf (-20)) (.leaf (-16)))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_193_2093 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (7)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (6)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (5)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (7))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (1)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (5)))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (3))))) (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (1)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (6)) (.leaf (5))))))))
  code := certificateD8_2093
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.branch 38 (.leaf (-5)) (.leaf (-6))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 39 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))),
  (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 33 (.leaf (-11)) (.branch 41 (.leaf (-10)) (.leaf (-8)))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_193_2094 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (7)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (3)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (6)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (7)) (.leaf (6)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (0)) (.leaf (6))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (3)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (7)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (3)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (5)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2094
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (-2))) (.branch 44 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-8)))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-4)),
  (.branch 42 (.branch 31 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 39 (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-11)) (.leaf (-10)))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_193_2095 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (5)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (7)) (.branch 21 (.leaf (2)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (1)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (2)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (4))))) (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_2095
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-37))) (.branch 24 (.leaf (-38)) (.branch 35 (.leaf (-39)) (.leaf (-40))))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 20 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 38 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-40)) (.leaf (-36))) (.branch 38 (.leaf (-32)) (.branch 39 (.leaf (-28)) (.leaf (-24))))) (.branch 42 (.branch 41 (.leaf (-20)) (.leaf (-16))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 41 (.branch 6 (.leaf (-25)) (.branch 40 (.leaf (-24)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-12))) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 34 (.branch 10 (.leaf (-27)) (.branch 33 (.leaf (-26)) (.leaf (-24)))) (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-20))) (.branch 37 (.leaf (-18)) (.leaf (-16))))) (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 21 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_193 : Fin 22 → CycleWitness 8 := ![witnessD8_193_2074, witnessD8_193_2075, witnessD8_193_2076, witnessD8_193_2077, witnessD8_193_2078, witnessD8_193_2079, witnessD8_193_2080, witnessD8_193_2081, witnessD8_193_2082, witnessD8_193_2083, witnessD8_193_2084, witnessD8_193_2085, witnessD8_193_2086, witnessD8_193_2087, witnessD8_193_2088, witnessD8_193_2089, witnessD8_193_2090, witnessD8_193_2091, witnessD8_193_2092, witnessD8_193_2093, witnessD8_193_2094, witnessD8_193_2095]
end RealPinwheel.FiveSixths


