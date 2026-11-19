-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_213
-- name    : RealPinwheel_FiveSixths_WitnessD8_213
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:55:29.581348+00:00
-- url     : https://prove2.me/theorems/a7edf731-57d7-43f0-b737-e6a5a481741b
-- title:
--   Exact witness block D8_213
-- statement:
--   These exact witnesses represent words 2541 through 2566 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2541–2566; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_213_2540 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (1))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (4))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (7)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (6)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_2540
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (-10)) (.leaf (-12))))]
  high := ![(.branch 30 (.branch 18 (.leaf (-17)) (.branch 24 (.leaf (-16)) (.leaf (-15)))) (.branch 37 (.branch 36 (.leaf (-14)) (.leaf (-11))) (.branch 38 (.leaf (-8)) (.leaf (-5))))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.branch 35 (.branch 19 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-15))) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.branch 37 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.branch 35 (.branch 20 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-13)))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-9))) (.branch 38 (.leaf (-7)) (.leaf (-5))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_213_2541 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (1)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (7)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (2)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (2)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2541
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 18 (.leaf (-12)) (.branch 29 (.leaf (-14)) (.leaf (-15))))),
  (.branch 33 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-24)) (.leaf (-25)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-16)) (.leaf (-18)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (-6)) (.leaf (-10))))]
  high := ![(.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.branch 36 (.branch 30 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-11)) (.branch 38 (.leaf (-8)) (.leaf (-5))))),
  (.branch 34 (.leaf (-3)) (.leaf (0))),
  (.branch 38 (.leaf (-5)) (.leaf (-4))),
  (.branch 36 (.branch 35 (.leaf (-25)) (.leaf (-20))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-1)),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-18)) (.leaf (-17))) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 29 (.leaf (-12)) (.leaf (-11))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.leaf (-7)))) (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2))))))),
  (.branch 35 (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8)))) (.branch 37 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-5)) (.leaf (-4)))))]
def witnessD8_213_2542 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (7))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2542
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-33)) (.leaf (-34)))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 31 (.leaf (-10)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-34)) (.leaf (-32))) (.branch 25 (.leaf (-30)) (.leaf (-28)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-24))) (.branch 29 (.leaf (-22)) (.leaf (-20))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-16))) (.branch 33 (.leaf (-14)) (.leaf (-12)))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 33 (.branch 30 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-16)) (.leaf (-14))))) (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_213_2543 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (7))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2543
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 17 (.leaf (0)) (.branch 36 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 37 (.branch 36 (.leaf (-12)) (.leaf (-9))) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 28 (.branch 7 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-24)))) (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-20))) (.branch 31 (.leaf (-18)) (.leaf (-16))))) (.branch 35 (.branch 33 (.leaf (-14)) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_213_2544 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_2544
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 25 (.leaf (0)) (.leaf (-14))),
  (.branch 38 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 36 (.leaf (-12)) (.leaf (-9))) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.leaf (-2)) (.leaf (0))),
  (.branch 33 (.leaf (-8)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 37 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-27)) (.branch 14 (.leaf (-26)) (.leaf (-25)))) (.branch 16 (.leaf (-24)) (.branch 17 (.leaf (-23)) (.leaf (-22))))) (.branch 21 (.branch 19 (.leaf (-21)) (.branch 20 (.leaf (-20)) (.leaf (-19)))) (.branch 23 (.branch 22 (.leaf (-18)) (.leaf (-17))) (.branch 24 (.leaf (-16)) (.leaf (-15)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_213_2545 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (6))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (7)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (6)) (.leaf (1))))))))
  code := certificateD8_2545
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-29)) (.leaf (-34)))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (-15)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-23))))]
  high := ![(.branch 29 (.branch 21 (.leaf (-34)) (.branch 25 (.leaf (-33)) (.leaf (-32)))) (.branch 37 (.branch 33 (.leaf (-31)) (.leaf (-30))) (.branch 38 (.leaf (-20)) (.leaf (-10))))),
  (.branch 24 (.branch 16 (.leaf (-3)) (.leaf (-2))) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2))))),
  (.branch 38 (.leaf (-3)) (.leaf (-2))),
  (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 35 (.branch 23 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 36 (.branch 35 (.leaf (-13)) (.leaf (-11))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-7)) (.leaf (-5))))))]
def witnessD8_213_2546 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (7)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (7))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (5)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (4)) (.leaf (7)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (6)) (.leaf (4))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2546
  counts := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-29)) (.leaf (-31)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.branch 38 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 36 (.branch 28 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.leaf (-5)) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 26 (.leaf (-31)) (.branch 34 (.leaf (-30)) (.leaf (-25)))) (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-15))) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.branch 13 (.leaf (-18)) (.branch 21 (.leaf (-17)) (.leaf (-16)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6))))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_213_2547 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (4)) (.leaf (0))))) (.branch 14 (.branch 11 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (6)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.leaf (5)))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (0))))) (.branch 33 (.branch 30 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (7)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_2547
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 15 (.leaf (9)) (.branch 16 (.leaf (10)) (.leaf (11)))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (12)) (.branch 21 (.leaf (13)) (.leaf (14)))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))) (.branch 32 (.branch 29 (.leaf (18)) (.branch 31 (.leaf (19)) (.leaf (20)))) (.branch 35 (.branch 34 (.leaf (21)) (.leaf (22))) (.branch 37 (.leaf (23)) (.leaf (24))))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.branch 22 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 33 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-7)))),
  (.branch 33 (.branch 18 (.branch 5 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 24 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213_2548 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 9 (.leaf (3)) (.leaf (0))))) (.branch 14 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.leaf (4)))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (0)))) (.branch 27 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 30 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (7))) (.branch 37 (.leaf (0)) (.leaf (4)))))))
  code := certificateD8_2548
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 15 (.leaf (9)) (.branch 16 (.leaf (10)) (.leaf (11)))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (12)) (.branch 21 (.leaf (13)) (.leaf (14)))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))) (.branch 32 (.branch 29 (.leaf (18)) (.branch 31 (.leaf (19)) (.leaf (20)))) (.branch 35 (.branch 34 (.leaf (21)) (.leaf (22))) (.branch 37 (.leaf (23)) (.leaf (24))))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.branch 22 (.leaf (-9)) (.leaf (-10))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-27))),
  (.branch 23 (.leaf (0)) (.leaf (-15))),
  (.branch 36 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 23 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-7)))),
  (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 33 (.branch 18 (.branch 5 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 24 (.branch 17 (.branch 14 (.branch 12 (.leaf (-27)) (.branch 13 (.leaf (-26)) (.leaf (-25)))) (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_213_2549 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (7)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2549
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.leaf (-8)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.leaf (-7)))),
  (.branch 19 (.leaf (0)) (.leaf (-19))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-29))),
  (.branch 28 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 27 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-13))))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 23 (.branch 16 (.branch 12 (.branch 10 (.leaf (-29)) (.branch 11 (.leaf (-28)) (.leaf (-27)))) (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23))))) (.branch 19 (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_213_2550 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (3)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.leaf (5)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2550
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-13))))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_213_2551 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (5)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2551
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 19 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-13))))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 33 (.branch 31 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_213_2552 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (3)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (2)) (.leaf (3)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (4)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2552
  counts := ![(.branch 15 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-26)) (.leaf (-35)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.leaf (-20))),
  (.branch 37 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 35 (.branch 22 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-30)) (.branch 37 (.leaf (-26)) (.leaf (-22))))),
  (.branch 20 (.leaf (-6)) (.branch 37 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16))))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_213_2553 : CycleWitness 8 where
  length := 38
  word := (.branch 20 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (7)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (5))) (.branch 9 (.leaf (0)) (.leaf (3))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (7)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (0))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (6)) (.branch 37 (.leaf (0)) (.leaf (1))))))))
  code := certificateD8_2553
  counts := ![(.branch 19 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (11)) (.leaf (12))) (.branch 24 (.leaf (13)) (.branch 26 (.leaf (14)) (.leaf (15))))) (.branch 33 (.branch 29 (.leaf (16)) (.branch 31 (.leaf (17)) (.leaf (18)))) (.branch 35 (.leaf (19)) (.branch 37 (.leaf (20)) (.leaf (21))))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.branch 27 (.leaf (-13)) (.leaf (-14))))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-5)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-16)) (.leaf (-21))))]
  high := ![(.branch 32 (.branch 28 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 34 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 31 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 29 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))) (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))))))]
def witnessD8_213_2554 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (3))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2554
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 21 (.leaf (-22)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-32))),
  (.branch 25 (.leaf (0)) (.leaf (-13))),
  (.branch 15 (.leaf (0)) (.leaf (-23))),
  (.branch 34 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.branch 22 (.leaf (-27)) (.branch 25 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.branch 31 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-22)) (.leaf (-16))))),
  (.branch 33 (.leaf (-5)) (.leaf (-4))),
  (.branch 36 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-32)) (.leaf (-31))) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_213_2555 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (3)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (2))) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (6)) (.leaf (1))))))))
  code := certificateD8_2555
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 21 (.leaf (-24)) (.leaf (-31)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-10)) (.leaf (-12)))),
  (.branch 26 (.leaf (0)) (.leaf (-12))),
  (.branch 37 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 29 (.branch 22 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-24)) (.leaf (-19))))),
  (.leaf (0)),
  (.branch 32 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 24 (.branch 17 (.branch 14 (.branch 12 (.leaf (-27)) (.branch 13 (.leaf (-26)) (.leaf (-25)))) (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_213_2556 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (7)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (3)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (0))) (.branch 32 (.leaf (2)) (.leaf (7)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2556
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.leaf (-23)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 27 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-13))))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 23 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.branch 31 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213_2557 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (7))) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_2557
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 28 (.branch 21 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13))))) (.branch 32 (.branch 30 (.leaf (14)) (.leaf (15))) (.branch 34 (.leaf (16)) (.branch 36 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-18)) (.leaf (-19)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-26))),
  (.branch 31 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 22 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-10)))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-26)) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 16 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21))))) (.branch 21 (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18)))) (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213_2558 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (6)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.leaf (7)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2558
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.leaf (-23)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 33 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 27 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-13))))),
  (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 23 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213_2559 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (3)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (7))) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2559
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 28 (.branch 21 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13))))) (.branch 32 (.branch 30 (.leaf (14)) (.leaf (15))) (.branch 34 (.leaf (16)) (.branch 36 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-18)) (.leaf (-19)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-35))),
  (.branch 22 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-26))),
  (.branch 31 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 22 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-10)))),
  (.leaf (-3)),
  (.branch 36 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 20 (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-35)) (.leaf (-34))) (.branch 6 (.leaf (-33)) (.leaf (-32)))) (.branch 9 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 10 (.leaf (-29)) (.leaf (-28))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-27)) (.leaf (-26))) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-14)) (.leaf (-13))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-26)) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 16 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21))))) (.branch 21 (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18)))) (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213_2560 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2560
  counts := ![(.branch 18 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13))))) (.branch 33 (.branch 31 (.leaf (14)) (.leaf (15))) (.branch 35 (.leaf (16)) (.branch 37 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-11)))) (.branch 7 (.leaf (-12)) (.branch 9 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-8))),
  (.branch 19 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 29 (.leaf (-14)) (.leaf (-9))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_213_2561 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (6)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_2561
  counts := ![(.branch 18 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 29 (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13))))) (.branch 33 (.branch 31 (.leaf (14)) (.leaf (15))) (.branch 35 (.leaf (16)) (.branch 37 (.leaf (17)) (.leaf (18))))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-11)) (.branch 7 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-15)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 27 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-30)))]
  high := ![(.branch 27 (.leaf (-13)) (.leaf (-9))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-14))) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.leaf (-30)) (.branch 10 (.leaf (-29)) (.leaf (-28)))) (.branch 13 (.branch 12 (.leaf (-27)) (.leaf (-26))) (.branch 14 (.leaf (-25)) (.leaf (-24))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_213_2562 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (6)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_2562
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-13)) (.branch 24 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.branch 34 (.leaf (-6)) (.leaf (-8))))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-25))),
  (.branch 32 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 31 (.branch 25 (.leaf (-20)) (.branch 28 (.leaf (-19)) (.leaf (-18)))) (.branch 34 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-11))))),
  (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 14 (.leaf (-25)) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20))))) (.branch 22 (.branch 20 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-17)))) (.branch 23 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213_2563 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (5)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (0))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_2563
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 20 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-14)))) (.branch 22 (.leaf (-15)) (.branch 25 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-23))),
  (.branch 34 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 36 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-12)) (.leaf (-8)))),
  (.branch 27 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.branch 25 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_213_2564 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (7)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_2564
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.leaf (0)) (.leaf (-22))),
  (.branch 35 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 26 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 35 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.leaf (-5)) (.leaf (-4))),
  (.branch 37 (.leaf (-6)) (.leaf (-3))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18))))) (.branch 24 (.branch 22 (.leaf (-17)) (.branch 23 (.leaf (-16)) (.leaf (-15)))) (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.leaf (-31)) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_213_2565 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (6)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (4)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (7)))) (.branch 35 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2565
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))) (.branch 33 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.leaf (13)))))),
  (.branch 20 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-25)) (.leaf (-37)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 29 (.branch 26 (.leaf (-5)) (.leaf (-6))) (.branch 35 (.leaf (-7)) (.leaf (-9))))),
  (.branch 25 (.branch 19 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 32 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-37)) (.branch 7 (.leaf (-36)) (.leaf (-35)))) (.branch 13 (.leaf (-34)) (.branch 16 (.leaf (-33)) (.leaf (-32))))) (.branch 28 (.branch 22 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 31 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-26)) (.leaf (-13)))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 29 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_213 : Fin 26 → CycleWitness 8 := ![witnessD8_213_2540, witnessD8_213_2541, witnessD8_213_2542, witnessD8_213_2543, witnessD8_213_2544, witnessD8_213_2545, witnessD8_213_2546, witnessD8_213_2547, witnessD8_213_2548, witnessD8_213_2549, witnessD8_213_2550, witnessD8_213_2551, witnessD8_213_2552, witnessD8_213_2553, witnessD8_213_2554, witnessD8_213_2555, witnessD8_213_2556, witnessD8_213_2557, witnessD8_213_2558, witnessD8_213_2559, witnessD8_213_2560, witnessD8_213_2561, witnessD8_213_2562, witnessD8_213_2563, witnessD8_213_2564, witnessD8_213_2565]
end RealPinwheel.FiveSixths


