-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_192
-- name    : RealPinwheel_FiveSixths_WitnessD8_192
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:36:39.884899+00:00
-- url     : https://prove2.me/theorems/4f4318c9-4163-45f6-ac51-326b576ed06b
-- title:
--   Exact witness block D8_192
-- statement:
--   These exact witnesses represent words 2054 through 2074 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2054–2074; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_192_2053 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (1)) (.leaf (4))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (4)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (3)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (4)))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 43 (.branch 41 (.leaf (7)) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2053
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-28))),
  (.branch 41 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 44 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 45 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10))))),
  (.branch 39 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-4)))),
  (.branch 43 (.branch 27 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 40 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 33 (.branch 31 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 32 (.leaf (-15)) (.leaf (-14)))) (.branch 35 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-11)) (.leaf (-10))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-7)) (.leaf (-6)))) (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 25 (.branch 21 (.branch 19 (.leaf (-28)) (.branch 20 (.leaf (-27)) (.leaf (-26)))) (.branch 23 (.branch 22 (.leaf (-25)) (.leaf (-24))) (.branch 24 (.leaf (-23)) (.leaf (-22))))) (.branch 28 (.branch 26 (.leaf (-21)) (.branch 27 (.leaf (-20)) (.leaf (-19)))) (.branch 30 (.branch 29 (.leaf (-18)) (.leaf (-17))) (.branch 31 (.leaf (-16)) (.leaf (-15)))))) (.branch 39 (.branch 35 (.branch 33 (.leaf (-14)) (.branch 34 (.leaf (-13)) (.leaf (-12)))) (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.leaf (-8))))) (.branch 42 (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_192_2054 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (6)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (5)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (7)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (4)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (6)) (.leaf (2))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (5)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (2)) (.branch 30 (.leaf (1)) (.leaf (7)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (4)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (3)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (6)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (5)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2054
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 33 (.leaf (-17)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-17)) (.leaf (-18)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-34))) (.branch 34 (.leaf (-35)) (.leaf (-36)))),
  (.branch 11 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-8)) (.leaf (-10)))),
  (.branch 31 (.leaf (0)) (.branch 45 (.leaf (-1)) (.leaf (-3))))]
  high := ![(.branch 33 (.branch 25 (.leaf (-17)) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.leaf (-6))))),
  (.branch 39 (.branch 34 (.leaf (-20)) (.leaf (-19))) (.branch 44 (.leaf (-18)) (.branch 45 (.leaf (-14)) (.leaf (-10))))),
  (.leaf (0)),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-18)) (.leaf (-16))) (.branch 40 (.leaf (-14)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-8))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 40 (.branch 37 (.branch 35 (.leaf (-36)) (.branch 36 (.leaf (-33)) (.leaf (-30)))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-24)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-15)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 40 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))) (.branch 44 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-3))]
def witnessD8_192_2055 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (7)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (4)) (.branch 19 (.leaf (6)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (5))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (7)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (6)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (5)) (.branch 36 (.leaf (0)) (.leaf (3)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (4)) (.branch 42 (.leaf (7)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2055
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 33 (.leaf (-17)) (.leaf (-20)))),
  (.branch 22 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-17)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-34))) (.branch 34 (.leaf (-35)) (.leaf (-36)))),
  (.branch 11 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 33 (.branch 25 (.leaf (-17)) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.leaf (-6))))),
  (.branch 39 (.branch 34 (.leaf (-20)) (.leaf (-19))) (.branch 44 (.leaf (-18)) (.branch 45 (.leaf (-14)) (.leaf (-10))))),
  (.leaf (-3)),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-18)) (.leaf (-16))) (.branch 40 (.leaf (-14)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-8))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 43 (.branch 30 (.leaf (-11)) (.branch 42 (.leaf (-10)) (.leaf (-8)))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 40 (.branch 37 (.branch 35 (.leaf (-36)) (.branch 36 (.leaf (-33)) (.leaf (-30)))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-24)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-15)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_192_2056 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (3)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (4)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (7))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (6)) (.branch 36 (.leaf (1)) (.leaf (3)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (3)) (.branch 45 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_2056
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 40 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 40 (.branch 20 (.leaf (-17)) (.leaf (-19))) (.branch 43 (.leaf (-21)) (.leaf (-23))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-15)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 32 (.leaf (-14)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-18)) (.leaf (-13)))),
  (.branch 43 (.branch 31 (.leaf (-18)) (.branch 37 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-12)) (.branch 45 (.leaf (-8)) (.leaf (-4))))),
  (.branch 34 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 45 (.leaf (-6)) (.leaf (-3))),
  (.branch 39 (.branch 35 (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 42 (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))) (.branch 44 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3))))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-11)) (.leaf (-10))) (.branch 38 (.leaf (-9)) (.branch 39 (.leaf (-8)) (.leaf (-7))))) (.branch 43 (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-5)) (.leaf (-4)))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_192_2057 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (6)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (5)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (7)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (4)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (6)) (.leaf (2)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (4)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (7)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (5)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2057
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 10 (.leaf (-10)) (.branch 33 (.leaf (-12)) (.leaf (-13))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))) (.branch 31 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 33 (.branch 25 (.leaf (-17)) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 41 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.leaf (-6))))),
  (.branch 39 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 44 (.leaf (-11)) (.branch 45 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-5)),
  (.leaf (0)),
  (.branch 39 (.branch 36 (.branch 4 (.leaf (-37)) (.branch 35 (.leaf (-36)) (.leaf (-33)))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-27)) (.leaf (-24))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-18)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.branch 34 (.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-11))) (.branch 37 (.leaf (-10)) (.leaf (-9))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_192_2058 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (5)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (4)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (4)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (7)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2058
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 27 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 16 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 39 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 33 (.leaf (-17)) (.leaf (-20)))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))) (.branch 31 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 11 (.leaf (0)) (.leaf (-35))),
  (.branch 26 (.leaf (0)) (.leaf (-20))),
  (.branch 42 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 40 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 39 (.branch 34 (.leaf (-20)) (.leaf (-19))) (.branch 44 (.leaf (-18)) (.branch 45 (.leaf (-14)) (.leaf (-10))))),
  (.leaf (-5)),
  (.branch 41 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 36 (.branch 4 (.leaf (-37)) (.branch 35 (.leaf (-36)) (.leaf (-33)))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-27)) (.leaf (-24))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-18)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 28 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-35)) (.leaf (-34))) (.branch 14 (.leaf (-33)) (.leaf (-32)))) (.branch 17 (.branch 16 (.leaf (-31)) (.leaf (-30))) (.branch 18 (.leaf (-29)) (.leaf (-28))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-27)) (.leaf (-26))) (.branch 22 (.leaf (-25)) (.leaf (-24)))) (.branch 25 (.branch 24 (.leaf (-23)) (.leaf (-22))) (.branch 26 (.leaf (-21)) (.branch 27 (.leaf (-20)) (.leaf (-19))))))) (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-18)) (.leaf (-17))) (.branch 31 (.leaf (-16)) (.leaf (-15)))) (.branch 34 (.branch 33 (.leaf (-14)) (.leaf (-13))) (.branch 35 (.leaf (-12)) (.branch 36 (.leaf (-11)) (.leaf (-10)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-7)) (.leaf (-6)))) (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 31 (.branch 28 (.branch 27 (.leaf (-20)) (.leaf (-19))) (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-17)) (.leaf (-16))))) (.branch 33 (.branch 32 (.leaf (-15)) (.leaf (-14))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-12)) (.leaf (-11)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (-10)) (.leaf (-9))) (.branch 39 (.leaf (-8)) (.branch 40 (.leaf (-7)) (.leaf (-6))))) (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_192_2059 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (7)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (5)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (1)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (7)) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (3)))) (.branch 38 (.leaf (2)) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 43 (.branch 41 (.leaf (6)) (.branch 42 (.leaf (5)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2059
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-11)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 14 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-37))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (-13)) (.leaf (-14)))),
  (.branch 18 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 44 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 45 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10))))),
  (.branch 39 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 40 (.leaf (-1)) (.leaf (0)))),
  (.branch 39 (.branch 36 (.branch 4 (.leaf (-37)) (.branch 35 (.leaf (-36)) (.leaf (-33)))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-27)) (.leaf (-24))))) (.branch 42 (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-18)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.branch 27 (.leaf (-14)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 33 (.branch 31 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 32 (.leaf (-15)) (.leaf (-14)))) (.branch 35 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-11)) (.leaf (-10))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-7)) (.leaf (-6)))) (.branch 43 (.branch 42 (.leaf (-5)) (.leaf (-4))) (.branch 44 (.leaf (-3)) (.branch 45 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_192_2060 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (7)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (6)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 21 (.leaf (3)) (.branch 22 (.leaf (7)) (.leaf (0))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (6)) (.leaf (0)))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (4)))) (.branch 38 (.leaf (7)) (.branch 39 (.leaf (0)) (.leaf (5))))) (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (6))))))))
  code := certificateD8_2060
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 41 (.leaf (9)) (.branch 45 (.leaf (10)) (.leaf (11)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 1 (.leaf (0)) (.leaf (-29))) (.branch 23 (.leaf (-34)) (.leaf (-43)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 36 (.leaf (-8)) (.leaf (-9)))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-9)) (.leaf (-14)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 21 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-19)) (.leaf (-26)))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (-16))) (.branch 40 (.leaf (-17)) (.leaf (-18)))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 36 (.branch 28 (.branch 24 (.leaf (-43)) (.leaf (-42))) (.branch 32 (.leaf (-41)) (.leaf (-40)))) (.branch 44 (.branch 40 (.leaf (-39)) (.leaf (-38))) (.branch 45 (.leaf (-28)) (.leaf (-18))))),
  (.branch 37 (.leaf (-9)) (.leaf (-8))),
  (.branch 35 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-10)))),
  (.branch 43 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-26)) (.leaf (-24))) (.branch 40 (.leaf (-22)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-18)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-12)) (.leaf (-10)))))),
  (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-15)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (0)))),
  (.branch 41 (.branch 23 (.branch 7 (.leaf (-19)) (.leaf (-18))) (.branch 39 (.leaf (-17)) (.branch 40 (.leaf (-15)) (.leaf (-13))))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-9))) (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-5)) (.leaf (-3))))))]
def witnessD8_192_2061 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (2)) (.leaf (1)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (4)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (2)) (.leaf (1)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (5))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (6))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (3)) (.leaf (5))))) (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 32 (.leaf (7)) (.branch 33 (.leaf (4)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (2)) (.leaf (1)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (5))))) (.branch 43 (.branch 41 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2061
  counts := ![(.branch 21 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 24 (.leaf (-5)) (.branch 38 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-5)) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (-13)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))),
  (.branch 38 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 44 (.leaf (-12)) (.branch 45 (.leaf (-8)) (.leaf (-4))))),
  (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 42 (.branch 29 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-10)))) (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.branch 24 (.leaf (-16)) (.leaf (-15))) (.branch 41 (.leaf (-13)) (.leaf (-11)))) (.branch 44 (.branch 43 (.leaf (-9)) (.leaf (-7))) (.branch 45 (.leaf (-5)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD8_192_2062 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (4)) (.leaf (6)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (3))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 21 (.leaf (7)) (.branch 22 (.leaf (1)) (.leaf (4))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (1)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (2)) (.branch 30 (.leaf (5)) (.leaf (6)))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (1)) (.leaf (0)))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (2)) (.leaf (3))))) (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 44 (.leaf (7)) (.branch 45 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2062
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 43 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-18))) (.branch 14 (.leaf (-21)) (.leaf (-22)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 22 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-16)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 40 (.leaf (-17)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 43 (.branch 38 (.leaf (-22)) (.leaf (-20))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 44 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-10)) (.leaf (-5)))),
  (.branch 43 (.branch 41 (.leaf (-22)) (.branch 42 (.leaf (-20)) (.leaf (-18)))) (.branch 44 (.leaf (-16)) (.branch 45 (.leaf (-14)) (.leaf (-12))))),
  (.branch 41 (.branch 39 (.branch 8 (.leaf (-25)) (.leaf (-24))) (.branch 40 (.leaf (-21)) (.leaf (-18)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 31 (.leaf (-2)) (.leaf (0))),
  (.branch 38 (.branch 34 (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-11))) (.branch 37 (.leaf (-10)) (.leaf (-9))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-7))) (.branch 41 (.leaf (-6)) (.leaf (-5)))) (.branch 44 (.branch 43 (.leaf (-4)) (.leaf (-3))) (.branch 45 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_192_2063 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (7)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (4)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (6)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (5))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (3)))) (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (7))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (5))))) (.branch 31 (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (6)))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (4)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (7)))) (.branch 38 (.leaf (1)) (.branch 39 (.leaf (3)) (.leaf (5))))) (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (2)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2063
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 25 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-8))) (.branch 37 (.leaf (-9)) (.leaf (-11))))]
  high := ![(.branch 43 (.branch 36 (.leaf (-21)) (.branch 42 (.leaf (-20)) (.leaf (-16)))) (.branch 44 (.leaf (-12)) (.branch 45 (.leaf (-8)) (.leaf (-4))))),
  (.branch 39 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-4)))),
  (.branch 37 (.branch 23 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 44 (.leaf (-11)) (.branch 45 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 43 (.branch 27 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 29 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-10)))) (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8)))) (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3))))))]
def witnessD8_192_2064 : CycleWitness 8 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (6)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (1)) (.leaf (3))))) (.branch 20 (.branch 18 (.leaf (5)) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (1)) (.leaf (6))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (2))))) (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (7)))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (4)) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 38 (.leaf (6)) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 43 (.branch 41 (.leaf (5)) (.branch 42 (.leaf (0)) (.leaf (4)))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2064
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 37 (.leaf (-20)) (.leaf (-23)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-22))) (.branch 38 (.leaf (-23)) (.leaf (-24)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 43 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-18)) (.branch 45 (.leaf (-14)) (.leaf (-10))))),
  (.branch 34 (.branch 28 (.leaf (-7)) (.leaf (-6))) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 37 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-3)))),
  (.branch 42 (.branch 33 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 27 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-8))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.branch 39 (.leaf (-24)) (.leaf (-21))) (.branch 41 (.leaf (-18)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-9))) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.leaf (-1)) (.leaf (0)))]
def witnessD8_192_2065 : CycleWitness 8 where
  length := 45
  word := (.branch 23 (.branch 12 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.branch 22 (.leaf (0)) (.leaf (3))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))))) (.branch 39 (.branch 37 (.branch 35 (.leaf (7)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 42 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_2065
  counts := ![(.branch 22 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 29 (.leaf (17)) (.leaf (18))) (.branch 32 (.leaf (19)) (.leaf (20))))) (.branch 39 (.branch 36 (.leaf (21)) (.branch 37 (.leaf (22)) (.leaf (23)))) (.branch 42 (.branch 41 (.leaf (24)) (.leaf (25))) (.branch 44 (.leaf (26)) (.leaf (27))))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-40))),
  (.branch 20 (.leaf (0)) (.leaf (-25))),
  (.branch 35 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 25 (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-40)) (.leaf (-39))) (.branch 8 (.leaf (-38)) (.branch 9 (.leaf (-37)) (.leaf (-36))))) (.branch 12 (.branch 11 (.leaf (-35)) (.leaf (-34))) (.branch 13 (.leaf (-33)) (.branch 14 (.leaf (-32)) (.leaf (-31)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-30)) (.leaf (-29))) (.branch 18 (.leaf (-28)) (.branch 19 (.leaf (-27)) (.leaf (-26))))) (.branch 22 (.branch 21 (.leaf (-25)) (.leaf (-24))) (.branch 23 (.leaf (-23)) (.branch 24 (.leaf (-22)) (.leaf (-21))))))) (.branch 35 (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.branch 29 (.leaf (-17)) (.leaf (-16))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-14))) (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 26 (.branch 23 (.branch 21 (.leaf (-25)) (.branch 22 (.leaf (-24)) (.leaf (-23)))) (.branch 24 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20))))) (.branch 29 (.branch 27 (.leaf (-19)) (.branch 28 (.leaf (-18)) (.leaf (-17)))) (.branch 30 (.leaf (-16)) (.branch 31 (.leaf (-15)) (.leaf (-14)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-11)))) (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-8))))) (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_192_2066 : CycleWitness 8 where
  length := 45
  word := (.branch 23 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 17 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (7)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (0))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (5))))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (6)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_2066
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 17 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))) (.branch 32 (.branch 27 (.branch 23 (.leaf (12)) (.branch 25 (.leaf (13)) (.leaf (14)))) (.branch 29 (.leaf (15)) (.branch 31 (.leaf (16)) (.leaf (17))))) (.branch 38 (.branch 34 (.leaf (18)) (.branch 36 (.leaf (19)) (.leaf (20)))) (.branch 42 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 44 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 13 (.leaf (0)) (.branch 35 (.leaf (-19)) (.leaf (-20)))),
  (.branch 20 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 37 (.branch 33 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 39 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.leaf (-8))))),
  (.branch 42 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 36 (.branch 31 (.branch 29 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 30 (.leaf (-32)) (.leaf (-30)))) (.branch 33 (.branch 32 (.leaf (-28)) (.leaf (-26))) (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-22)) (.leaf (-20)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-16))) (.branch 39 (.leaf (-14)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-18))) (.branch 38 (.leaf (-16)) (.branch 39 (.leaf (-14)) (.leaf (-12))))) (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 21 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_192_2067 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (6)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (7))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2067
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 33 (.branch 26 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13))))) (.branch 38 (.branch 35 (.leaf (14)) (.leaf (15))) (.branch 41 (.leaf (16)) (.branch 43 (.leaf (17)) (.leaf (18))))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 15 (.leaf (0)) (.branch 37 (.leaf (-15)) (.leaf (-16)))),
  (.branch 22 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 36 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 33 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 33 (.branch 31 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 32 (.leaf (-28)) (.leaf (-26)))) (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-22))) (.branch 36 (.leaf (-20)) (.leaf (-18))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-16)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-16)) (.leaf (-14))) (.branch 40 (.leaf (-12)) (.leaf (-10)))) (.branch 43 (.branch 42 (.leaf (-8)) (.leaf (-6))) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0)))]
def witnessD8_192_2068 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (7)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (2)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (7)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (2)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (1))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_2068
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.leaf (15)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-29))) (.branch 26 (.leaf (-30)) (.leaf (-31)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-13))) (.branch 30 (.leaf (-14)) (.branch 41 (.leaf (-15)) (.leaf (-16))))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-8)))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.leaf (-4)) (.leaf (-2))),
  (.branch 41 (.branch 39 (.branch 27 (.leaf (-31)) (.leaf (-28))) (.branch 40 (.leaf (-24)) (.leaf (-20)))) (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-12))) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-12))) (.branch 44 (.leaf (-8)) (.leaf (-4)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_192_2069 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (3)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (6)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1))))) (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2069
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-16))),
  (.branch 44 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-8)) (.leaf (-4))))),
  (.branch 40 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.leaf (-4)))),
  (.branch 38 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 21 (.branch 17 (.branch 15 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29)))) (.branch 19 (.branch 18 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-24)) (.leaf (-23))) (.branch 24 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.leaf (-17)))))) (.branch 37 (.branch 33 (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 33 (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_192_2070 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (7)) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0))))) (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2070
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))) (.branch 39 (.branch 35 (.leaf (10)) (.leaf (11))) (.branch 42 (.leaf (12)) (.leaf (13)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 33 (.branch 27 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))) (.branch 40 (.branch 38 (.leaf (10)) (.leaf (11))) (.branch 44 (.leaf (12)) (.leaf (13)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-32))) (.branch 28 (.leaf (-38)) (.leaf (-41)))),
  (.branch 19 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.leaf (-4)))) (.branch 33 (.branch 30 (.leaf (-5)) (.leaf (-6))) (.branch 40 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-21)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-9)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-32))),
  (.branch 34 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-41)) (.leaf (-40))) (.branch 43 (.leaf (-39)) (.branch 44 (.leaf (-26)) (.leaf (-13))))),
  (.leaf (-8)),
  (.branch 32 (.branch 15 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-19)) (.branch 44 (.leaf (-16)) (.leaf (-8))))),
  (.branch 42 (.branch 18 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 43 (.leaf (-8)) (.branch 44 (.leaf (-6)) (.leaf (-4))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-9)) (.leaf (-8))) (.branch 39 (.leaf (-7)) (.leaf (-6)))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 29 (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-32)) (.leaf (-31))) (.branch 16 (.leaf (-30)) (.leaf (-29)))) (.branch 19 (.branch 18 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-24)) (.leaf (-23))) (.branch 24 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-19))) (.branch 28 (.leaf (-18)) (.leaf (-17)))))) (.branch 37 (.branch 33 (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-15))) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 42 (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_192_2071 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0))))) (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2071
  counts := ![(.branch 22 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 38 (.leaf (7)) (.branch 43 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 33 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.branch 39 (.leaf (-7)) (.leaf (-6))))) (.branch 42 (.branch 41 (.leaf (-5)) (.leaf (-4))) (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 22 (.branch 18 (.branch 16 (.leaf (-30)) (.branch 17 (.leaf (-29)) (.leaf (-28)))) (.branch 20 (.branch 19 (.leaf (-27)) (.leaf (-26))) (.branch 21 (.leaf (-25)) (.leaf (-24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))))) (.branch 37 (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_192_2072 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (6)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (2))))) (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_2072
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 29 (.leaf (5)) (.leaf (6))) (.branch 39 (.leaf (7)) (.branch 44 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-30))),
  (.branch 30 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 22 (.branch 18 (.branch 16 (.leaf (-30)) (.branch 17 (.leaf (-29)) (.leaf (-28)))) (.branch 20 (.branch 19 (.leaf (-27)) (.leaf (-26))) (.branch 21 (.leaf (-25)) (.leaf (-24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 29 (.leaf (-17)) (.leaf (-16)))))) (.branch 37 (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-14)) (.leaf (-13)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_192_2073 : CycleWitness 8 where
  length := 45
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (7)) (.branch 21 (.leaf (0)) (.leaf (1))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (5)) (.branch 29 (.leaf (0)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 39 (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (0))))) (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (7)) (.branch 44 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_2073
  counts := ![(.branch 21 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 34 (.branch 26 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13))))) (.branch 39 (.branch 36 (.leaf (14)) (.leaf (15))) (.branch 41 (.leaf (16)) (.branch 44 (.leaf (17)) (.leaf (18))))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 37 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-35))),
  (.branch 13 (.leaf (0)) (.branch 35 (.leaf (-19)) (.leaf (-20)))),
  (.branch 20 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 42 (.leaf (-3)) (.leaf (-2))),
  (.branch 43 (.leaf (-3)) (.branch 44 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 43 (.branch 42 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 36 (.branch 31 (.branch 29 (.branch 6 (.leaf (-35)) (.leaf (-34))) (.branch 30 (.leaf (-32)) (.leaf (-30)))) (.branch 33 (.branch 32 (.leaf (-28)) (.leaf (-26))) (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-22)) (.leaf (-20)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-18)) (.leaf (-16))) (.branch 39 (.leaf (-14)) (.leaf (-12)))) (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 40 (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-18))) (.branch 38 (.leaf (-16)) (.branch 39 (.leaf (-14)) (.leaf (-12))))) (.branch 42 (.branch 41 (.leaf (-10)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 21 (.leaf (-5)) (.branch 44 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_192 : Fin 21 → CycleWitness 8 := ![witnessD8_192_2053, witnessD8_192_2054, witnessD8_192_2055, witnessD8_192_2056, witnessD8_192_2057, witnessD8_192_2058, witnessD8_192_2059, witnessD8_192_2060, witnessD8_192_2061, witnessD8_192_2062, witnessD8_192_2063, witnessD8_192_2064, witnessD8_192_2065, witnessD8_192_2066, witnessD8_192_2067, witnessD8_192_2068, witnessD8_192_2069, witnessD8_192_2070, witnessD8_192_2071, witnessD8_192_2072, witnessD8_192_2073]
end RealPinwheel.FiveSixths


