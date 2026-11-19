-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_163
-- name    : RealPinwheel_FiveSixths_WitnessD8_163
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:22:34.328482+00:00
-- url     : https://prove2.me/theorems/d14e872f-cd5a-4174-a2ef-6c0f7dc0d46a
-- title:
--   Exact witness block D8_163
-- statement:
--   These exact witnesses represent words 1515 through 1531 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1515–1531; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_163_1514 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (6))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (3))) (.branch 49 (.leaf (0)) (.leaf (4))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (2))) (.branch 53 (.leaf (0)) (.leaf (3)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1514
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 39 (.leaf (9)) (.leaf (10)))) (.branch 51 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 55 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 30 (.leaf (-18)) (.branch 33 (.leaf (-21)) (.leaf (-25))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))) (.branch 13 (.leaf (-11)) (.branch 42 (.leaf (-16)) (.leaf (-19))))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-15))),
  (.branch 29 (.leaf (0)) (.leaf (-29))),
  (.leaf (0))]
  high := ![(.branch 34 (.leaf (-25)) (.branch 57 (.leaf (-24)) (.leaf (-19)))),
  (.branch 56 (.branch 43 (.leaf (-19)) (.leaf (-18))) (.branch 57 (.leaf (-14)) (.leaf (-10)))),
  (.leaf (-5)),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 46 (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (-29)) (.branch 31 (.leaf (-28)) (.leaf (-27)))) (.branch 34 (.branch 33 (.leaf (-26)) (.leaf (-25))) (.branch 35 (.leaf (-24)) (.leaf (-23))))) (.branch 39 (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20)))) (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_163_1515 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (7))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1515
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 51 (.branch 46 (.leaf (11)) (.leaf (12))) (.branch 55 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))) (.branch 43 (.branch 17 (.leaf (-18)) (.leaf (-25))) (.branch 46 (.leaf (-27)) (.leaf (-34))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (-31))) (.branch 47 (.leaf (-32)) (.leaf (-33)))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-22))),
  (.branch 21 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 53 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 56 (.branch 47 (.leaf (-34)) (.leaf (-33))) (.branch 57 (.leaf (-28)) (.leaf (-23)))),
  (.leaf (0)),
  (.branch 55 (.branch 43 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-33)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 19 (.leaf (-4)) (.leaf (-3))),
  (.branch 47 (.branch 41 (.branch 38 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-20)) (.branch 40 (.leaf (-19)) (.leaf (-18))))) (.branch 44 (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_163_1516 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (7)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (6)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (5)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (7)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_1516
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 44 (.leaf (-25)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.leaf (-19)))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (-10)) (.leaf (-13)))),
  (.branch 40 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 20 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 49 (.branch 45 (.leaf (-30)) (.leaf (-28))) (.branch 53 (.leaf (-26)) (.branch 57 (.leaf (-24)) (.leaf (-17))))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-3)),
  (.branch 55 (.branch 47 (.leaf (-19)) (.leaf (-16))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 54 (.branch 52 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 46 (.branch 40 (.branch 37 (.branch 36 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_163_1517 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (6))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (7))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (2))) (.branch 49 (.leaf (0)) (.leaf (4))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (7))) (.branch 53 (.leaf (3)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (1))) (.branch 57 (.leaf (4)) (.leaf (5))))))))
  code := certificateD8_1517
  counts := ![(.branch 25 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-23)) (.leaf (-27)))),
  (.branch 2 (.leaf (0)) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 38 (.leaf (-17)) (.leaf (-18)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-19)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 50 (.branch 40 (.leaf (-27)) (.branch 45 (.leaf (-26)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-24)) (.leaf (-18))) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 57 (.leaf (-4)) (.leaf (-3))),
  (.branch 56 (.branch 41 (.leaf (-14)) (.leaf (-12))) (.branch 57 (.leaf (-8)) (.leaf (-4)))),
  (.branch 55 (.branch 39 (.leaf (-18)) (.branch 54 (.leaf (-17)) (.leaf (-14)))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 43 (.leaf (-6)) (.leaf (-5))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 47 (.branch 24 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-15))) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 55 (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))))]
def witnessD8_163_1518 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (7)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (0))) (.branch 35 (.leaf (6)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (7)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (5)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (3))) (.branch 49 (.leaf (6)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (2))) (.branch 53 (.leaf (1)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (3)) (.leaf (5))) (.branch 57 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1518
  counts := ![(.branch 25 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (7)) (.leaf (8))) (.branch 38 (.leaf (9)) (.leaf (10)))) (.branch 50 (.branch 46 (.leaf (11)) (.leaf (12))) (.branch 54 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))) (.branch 12 (.leaf (-15)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 47 (.leaf (-6)) (.leaf (-7)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-38)) (.leaf (-39)))),
  (.branch 33 (.branch 10 (.leaf (0)) (.leaf (-8))) (.branch 56 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 55 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-14)) (.leaf (-10))))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 45 (.branch 37 (.leaf (-3)) (.leaf (-2))) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 56 (.branch 33 (.leaf (-11)) (.leaf (-10))) (.branch 57 (.leaf (-8)) (.leaf (-6)))),
  (.branch 53 (.branch 40 (.branch 28 (.leaf (-39)) (.leaf (-37))) (.branch 52 (.leaf (-35)) (.leaf (-30)))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 57 (.leaf (-10)) (.leaf (-5))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-18)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_163_1519 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (4))) (.branch 24 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (7))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (6))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (4)) (.leaf (7)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (5))) (.branch 49 (.leaf (2)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (6)) (.leaf (4))) (.branch 53 (.leaf (3)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (2))) (.branch 57 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1519
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-27)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-40)) (.leaf (-44)))),
  (.branch 38 (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))) (.branch 44 (.leaf (-14)) (.branch 49 (.leaf (-18)) (.leaf (-27))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-30)) (.leaf (-39)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 18 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.branch 57 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 41 (.branch 26 (.branch 21 (.leaf (-30)) (.leaf (-29))) (.branch 31 (.leaf (-28)) (.branch 36 (.leaf (-27)) (.leaf (-26))))) (.branch 51 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 56 (.leaf (-23)) (.branch 57 (.leaf (-16)) (.leaf (-9)))))),
  (.branch 48 (.branch 22 (.branch 9 (.leaf (-44)) (.leaf (-43))) (.branch 35 (.leaf (-42)) (.leaf (-41)))) (.branch 56 (.branch 55 (.leaf (-36)) (.leaf (-27))) (.branch 57 (.leaf (-18)) (.leaf (-9))))),
  (.branch 50 (.leaf (-27)) (.branch 57 (.leaf (-26)) (.leaf (-21)))),
  (.branch 54 (.branch 10 (.leaf (-39)) (.branch 32 (.leaf (-38)) (.leaf (-37)))) (.branch 56 (.branch 55 (.leaf (-30)) (.leaf (-23))) (.branch 57 (.leaf (-16)) (.leaf (-9))))),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessD8_163_1520 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (2)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (1))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (2))) (.branch 28 (.leaf (6)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (2))) (.branch 35 (.leaf (0)) (.leaf (7))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (4))) (.branch 42 (.leaf (2)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (2))) (.branch 49 (.leaf (0)) (.leaf (4))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (7)) (.leaf (1))) (.branch 53 (.leaf (5)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (3)) (.leaf (2))) (.branch 57 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_1520
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-26)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 16 (.leaf (-22)) (.branch 23 (.leaf (-23)) (.leaf (-24))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 48 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.branch 47 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 55 (.branch 45 (.leaf (-26)) (.branch 50 (.leaf (-25)) (.leaf (-24)))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 55 (.branch 53 (.leaf (-24)) (.branch 54 (.leaf (-20)) (.leaf (-16)))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 49 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 47 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-7)) (.leaf (-5))))),
  (.branch 42 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (0)))),
  (.branch 54 (.branch 34 (.leaf (-17)) (.branch 44 (.leaf (-16)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_163_1521 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (7)) (.leaf (0))) (.branch 35 (.leaf (5)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (5))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (7)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (3)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_1521
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-19)) (.leaf (-23)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-14)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 46 (.leaf (-8)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 4 (.leaf (0)) (.leaf (-46))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (-16)) (.leaf (-17))))]
  high := ![(.branch 42 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 53 (.leaf (-19)) (.branch 57 (.leaf (-16)) (.leaf (-8))))),
  (.branch 49 (.branch 37 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 48 (.branch 33 (.leaf (-14)) (.leaf (-13))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 47 (.leaf (-13)) (.leaf (-12))),
  (.branch 53 (.branch 51 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 5 (.leaf (-46)) (.leaf (-45))) (.branch 45 (.leaf (-42)) (.leaf (-39)))) (.branch 48 (.branch 47 (.leaf (-36)) (.leaf (-33))) (.branch 49 (.leaf (-30)) (.leaf (-27))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-24)) (.leaf (-21))) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 34 (.leaf (-17)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_163_1522 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (7))) (.branch 28 (.leaf (1)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (5)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (3))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (2)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (6))) (.branch 57 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1522
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 45 (.branch 36 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 54 (.branch 49 (.leaf (11)) (.leaf (12))) (.branch 57 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 14 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 48 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-10)) (.branch 47 (.leaf (-12)) (.leaf (-13))))),
  (.branch 28 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 31 (.leaf (-14)) (.branch 57 (.leaf (-21)) (.leaf (-23))))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.leaf (-49))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (-19)) (.leaf (-20)))),
  (.branch 17 (.leaf (0)) (.branch 56 (.leaf (-3)) (.leaf (-4)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-11))) (.branch 46 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 52 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-23)),
  (.branch 49 (.branch 44 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 51 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 49 (.branch 45 (.branch 43 (.branch 4 (.leaf (-49)) (.leaf (-48))) (.branch 44 (.leaf (-45)) (.leaf (-42)))) (.branch 47 (.branch 46 (.leaf (-39)) (.leaf (-36))) (.branch 48 (.leaf (-33)) (.leaf (-30))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-27)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 54 (.branch 33 (.leaf (-20)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-4)) (.leaf (-3))),
  (.branch 52 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 50 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))))]
def witnessD8_163_1523 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (6))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (7)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (3)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (6)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (5)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1523
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 44 (.leaf (-25)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-23)) (.leaf (-24)))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (-10)) (.leaf (-13)))),
  (.branch 40 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 49 (.branch 45 (.leaf (-30)) (.leaf (-28))) (.branch 53 (.leaf (-26)) (.branch 57 (.leaf (-24)) (.leaf (-17))))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-3)),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-18)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 52 (.branch 49 (.branch 47 (.leaf (-24)) (.branch 48 (.leaf (-22)) (.leaf (-20)))) (.branch 50 (.leaf (-18)) (.branch 51 (.leaf (-16)) (.leaf (-14))))) (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-10)) (.leaf (-8)))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 55 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 54 (.branch 52 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))]
def witnessD8_163_1524 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (7)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (0))) (.branch 35 (.leaf (5)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (4)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (2))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (7)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1524
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 30 (.leaf (-8)) (.leaf (-9)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 48 (.leaf (-5)) (.leaf (-6)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 50 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 28 (.leaf (-7)) (.branch 51 (.leaf (-8)) (.leaf (-9))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 42 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 56 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 51 (.leaf (-4)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 52 (.branch 49 (.branch 33 (.leaf (-23)) (.branch 48 (.leaf (-22)) (.leaf (-20)))) (.branch 50 (.leaf (-18)) (.branch 51 (.leaf (-16)) (.leaf (-14))))) (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-10)) (.leaf (-8)))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 55 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_163_1525 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (7)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (3))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (4)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (0))) (.branch 57 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1525
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-25)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 53 (.leaf (-15)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-43)) (.leaf (-46)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-13))) (.branch 43 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 53 (.leaf (-19)) (.branch 57 (.leaf (-16)) (.leaf (-8))))),
  (.branch 37 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 53 (.branch 51 (.branch 41 (.leaf (-25)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-18))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 50 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 51 (.leaf (-40)) (.branch 52 (.leaf (-35)) (.leaf (-30))))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 56 (.branch 44 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 43 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_163_1526 : CycleWitness 8 where
  length := 57
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (6)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 25 (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (0))))))) (.branch 43 (.branch 35 (.branch 32 (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (3)))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (5))) (.branch 42 (.leaf (1)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 53 (.branch 51 (.leaf (4)) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1526
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 34 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 48 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 53 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 55 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.branch 40 (.leaf (-23)) (.leaf (-26))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.branch 54 (.leaf (-8)) (.leaf (-9))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-45))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-25)) (.leaf (-26)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (-5))) (.branch 41 (.leaf (-6)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 41 (.leaf (-26)) (.leaf (-25))) (.branch 51 (.leaf (-24)) (.branch 56 (.leaf (-23)) (.leaf (-16))))),
  (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-7)) (.leaf (-5)))),
  (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 51 (.branch 48 (.branch 4 (.leaf (-45)) (.branch 47 (.leaf (-44)) (.leaf (-40)))) (.branch 49 (.leaf (-36)) (.branch 50 (.leaf (-32)) (.leaf (-28))))) (.branch 54 (.branch 52 (.leaf (-24)) (.branch 53 (.leaf (-20)) (.leaf (-16)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 53 (.branch 23 (.leaf (-26)) (.branch 52 (.leaf (-24)) (.leaf (-20)))) (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-7)) (.leaf (-4))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_163_1527 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (0))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (6)) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (7)) (.leaf (4))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1527
  counts := ![(.branch 28 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))) (.branch 24 (.branch 22 (.leaf (10)) (.leaf (11))) (.branch 26 (.leaf (12)) (.leaf (13)))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (14)) (.branch 33 (.leaf (15)) (.leaf (16)))) (.branch 39 (.branch 37 (.leaf (17)) (.leaf (18))) (.branch 41 (.leaf (19)) (.leaf (20))))) (.branch 50 (.branch 45 (.leaf (21)) (.branch 47 (.leaf (22)) (.leaf (23)))) (.branch 54 (.branch 52 (.leaf (24)) (.leaf (25))) (.branch 56 (.leaf (26)) (.leaf (27))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-11)))) (.branch 7 (.leaf (-12)) (.branch 9 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 44 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-47))),
  (.branch 29 (.leaf (0)) (.leaf (-28))),
  (.branch 48 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 48 (.leaf (-14)) (.leaf (-9))),
  (.branch 54 (.branch 47 (.leaf (-14)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 45 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 39 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-47)) (.leaf (-46))) (.branch 13 (.leaf (-45)) (.branch 14 (.leaf (-44)) (.leaf (-43))))) (.branch 18 (.branch 16 (.leaf (-42)) (.branch 17 (.leaf (-41)) (.leaf (-40)))) (.branch 19 (.leaf (-39)) (.branch 20 (.leaf (-38)) (.leaf (-37)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-36)) (.branch 23 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31))))) (.branch 30 (.branch 28 (.leaf (-30)) (.branch 29 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-23)) (.leaf (-22)))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19))))) (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-26)))) (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-24))) (.branch 35 (.leaf (-23)) (.leaf (-22))))) (.branch 39 (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19)))) (.branch 41 (.branch 40 (.leaf (-18)) (.leaf (-17))) (.branch 42 (.leaf (-16)) (.leaf (-15)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_163_1528 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (7))) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1528
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 41 (.branch 34 (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 48 (.branch 43 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20)))) (.branch 53 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 56 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-9)))) (.branch 24 (.leaf (-11)) (.branch 43 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-48))),
  (.branch 28 (.leaf (0)) (.leaf (-29))),
  (.branch 47 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-11)) (.leaf (-8)))),
  (.branch 50 (.branch 45 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 46 (.leaf (-5)) (.branch 56 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 43 (.leaf (-11)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 39 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-48)) (.branch 11 (.leaf (-47)) (.leaf (-46)))) (.branch 13 (.leaf (-45)) (.branch 14 (.leaf (-44)) (.leaf (-43))))) (.branch 18 (.branch 16 (.leaf (-42)) (.branch 17 (.leaf (-41)) (.leaf (-40)))) (.branch 19 (.leaf (-39)) (.branch 20 (.leaf (-38)) (.leaf (-37)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-36)) (.branch 23 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31))))) (.branch 30 (.branch 28 (.leaf (-30)) (.branch 29 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-23)) (.leaf (-22)))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19))))) (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-29)) (.branch 30 (.leaf (-28)) (.leaf (-27)))) (.branch 33 (.branch 32 (.leaf (-26)) (.leaf (-25))) (.branch 34 (.leaf (-24)) (.leaf (-23))))) (.branch 38 (.branch 36 (.leaf (-22)) (.branch 37 (.leaf (-21)) (.leaf (-20)))) (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_163_1529 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (6)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (7))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1529
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 41 (.branch 35 (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 48 (.branch 43 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20)))) (.branch 54 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 56 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 22 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))) (.branch 41 (.branch 24 (.leaf (-6)) (.leaf (-7))) (.branch 43 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-46))),
  (.branch 30 (.leaf (0)) (.leaf (-27))),
  (.branch 49 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 49 (.leaf (-9)) (.leaf (-8))),
  (.branch 54 (.branch 41 (.leaf (-13)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.leaf (-2)) (.leaf (0))),
  (.branch 46 (.leaf (-5)) (.branch 56 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 43 (.leaf (-11)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-46)) (.leaf (-45))) (.branch 14 (.leaf (-44)) (.branch 15 (.leaf (-43)) (.leaf (-42))))) (.branch 19 (.branch 17 (.leaf (-41)) (.branch 18 (.leaf (-40)) (.leaf (-39)))) (.branch 20 (.leaf (-38)) (.branch 21 (.leaf (-37)) (.leaf (-36)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-35)) (.branch 24 (.leaf (-34)) (.leaf (-33)))) (.branch 26 (.leaf (-32)) (.branch 27 (.leaf (-31)) (.leaf (-30))))) (.branch 31 (.branch 29 (.leaf (-29)) (.branch 30 (.leaf (-28)) (.leaf (-27)))) (.branch 32 (.leaf (-26)) (.branch 33 (.leaf (-25)) (.leaf (-24))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-23)) (.leaf (-22))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19))))) (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 36 (.branch 33 (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-23)) (.leaf (-22))))) (.branch 39 (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19)))) (.branch 41 (.branch 40 (.leaf (-18)) (.leaf (-17))) (.branch 42 (.leaf (-16)) (.leaf (-15)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_163_1530 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (7)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1530
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 42 (.branch 35 (.branch 30 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 49 (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20)))) (.branch 54 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 56 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 31 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.branch 38 (.leaf (-18)) (.leaf (-22)))),
  (.branch 19 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 47 (.leaf (-12)) (.branch 52 (.leaf (-10)) (.leaf (-8)))),
  (.branch 54 (.branch 41 (.leaf (-13)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-7)) (.leaf (-5)))),
  (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 41 (.leaf (-20)) (.leaf (-19)))) (.branch 44 (.branch 43 (.leaf (-18)) (.leaf (-17))) (.branch 45 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))))),
  (.branch 53 (.branch 51 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (0))]
def witnessD8_163 : Fin 17 → CycleWitness 8 := ![witnessD8_163_1514, witnessD8_163_1515, witnessD8_163_1516, witnessD8_163_1517, witnessD8_163_1518, witnessD8_163_1519, witnessD8_163_1520, witnessD8_163_1521, witnessD8_163_1522, witnessD8_163_1523, witnessD8_163_1524, witnessD8_163_1525, witnessD8_163_1526, witnessD8_163_1527, witnessD8_163_1528, witnessD8_163_1529, witnessD8_163_1530]
end RealPinwheel.FiveSixths


