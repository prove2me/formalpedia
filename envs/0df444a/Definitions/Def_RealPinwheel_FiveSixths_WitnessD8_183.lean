-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_183
-- name    : RealPinwheel_FiveSixths_WitnessD8_183
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:33:01.016967+00:00
-- url     : https://prove2.me/theorems/eb576c41-6b02-4119-bc51-82cbd9c3d3f3
-- title:
--   Exact witness block D8_183
-- statement:
--   These exact witnesses represent words 1874 through 1892 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1874–1892; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_183_1873 : CycleWitness 8 where
  length := 51
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (1)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (3))))))) (.branch 38 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (1)))) (.branch 29 (.leaf (7)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (3)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (6))) (.branch 37 (.leaf (1)) (.leaf (2)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (4)) (.leaf (1)))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (0)) (.leaf (5))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (7)) (.leaf (2)))) (.branch 49 (.branch 48 (.leaf (0)) (.leaf (6))) (.branch 50 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1873
  counts := ![(.branch 22 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 27 (.leaf (-43)) (.leaf (-45)))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-27)) (.leaf (-28)))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 49 (.branch 44 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-7)) (.leaf (-4))),
  (.branch 48 (.branch 39 (.leaf (-9)) (.leaf (-8))) (.branch 49 (.leaf (-6)) (.branch 50 (.leaf (-4)) (.leaf (-2))))),
  (.branch 43 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 42 (.branch 28 (.leaf (-45)) (.branch 41 (.leaf (-44)) (.leaf (-40)))) (.branch 43 (.leaf (-36)) (.branch 44 (.leaf (-32)) (.leaf (-28))))) (.branch 48 (.branch 46 (.leaf (-24)) (.branch 47 (.leaf (-20)) (.leaf (-16)))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 47 (.branch 45 (.leaf (-28)) (.branch 46 (.leaf (-24)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-12))) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 24 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-4))))),
  (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_183_1874 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (3)) (.leaf (1))))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (5)) (.branch 36 (.leaf (1)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (3))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (7)))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_1874
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (11)) (.branch 27 (.leaf (12)) (.leaf (13)))) (.branch 31 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))) (.branch 44 (.branch 38 (.leaf (17)) (.branch 41 (.leaf (18)) (.leaf (19)))) (.branch 45 (.leaf (20)) (.branch 48 (.leaf (21)) (.leaf (22))))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 6 (.leaf (-6)) (.branch 13 (.leaf (-8)) (.leaf (-9))))) (.branch 31 (.branch 27 (.leaf (-10)) (.leaf (-11))) (.branch 38 (.leaf (-13)) (.branch 45 (.leaf (-14)) (.leaf (-15)))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (-9))) (.branch 40 (.leaf (-10)) (.leaf (-11)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-15))),
  (.branch 22 (.leaf (0)) (.leaf (-28))),
  (.branch 47 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 46 (.leaf (-15)) (.branch 49 (.leaf (-14)) (.leaf (-12)))),
  (.branch 29 (.leaf (-4)) (.branch 47 (.leaf (-3)) (.leaf (0)))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.branch 42 (.branch 38 (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 29 (.branch 25 (.branch 23 (.leaf (-28)) (.branch 24 (.leaf (-27)) (.leaf (-26)))) (.branch 27 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-23)) (.leaf (-22))))) (.branch 32 (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19)))) (.branch 34 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))))) (.branch 43 (.branch 39 (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_183_1875 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (1))))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 33 (.leaf (6)) (.leaf (0))) (.branch 35 (.leaf (3)) (.branch 36 (.leaf (1)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (1)) (.leaf (4))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1))))) (.branch 47 (.branch 45 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (3)))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1875
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (11)) (.branch 27 (.leaf (12)) (.leaf (13)))) (.branch 31 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))) (.branch 44 (.branch 38 (.leaf (17)) (.branch 41 (.leaf (18)) (.leaf (19)))) (.branch 45 (.leaf (20)) (.branch 48 (.leaf (21)) (.leaf (22))))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 6 (.leaf (-6)) (.branch 13 (.leaf (-8)) (.leaf (-9))))) (.branch 31 (.branch 27 (.leaf (-10)) (.leaf (-11))) (.branch 38 (.leaf (-13)) (.branch 45 (.leaf (-14)) (.leaf (-15)))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (-9))) (.branch 40 (.leaf (-10)) (.leaf (-11)))),
  (.branch 15 (.leaf (0)) (.leaf (-35))),
  (.branch 33 (.leaf (0)) (.leaf (-17))),
  (.branch 49 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 46 (.leaf (-15)) (.branch 49 (.leaf (-14)) (.leaf (-12)))),
  (.branch 29 (.leaf (-4)) (.branch 47 (.leaf (-3)) (.leaf (0)))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.branch 42 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 43 (.leaf (-9)) (.branch 44 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 32 (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-35)) (.leaf (-34))) (.branch 18 (.leaf (-33)) (.leaf (-32)))) (.branch 21 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 22 (.leaf (-29)) (.leaf (-28))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-27)) (.leaf (-26))) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 29 (.branch 28 (.leaf (-23)) (.leaf (-22))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19))))))) (.branch 41 (.branch 36 (.branch 34 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 38 (.branch 37 (.leaf (-14)) (.leaf (-13))) (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_183_1876 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (7)) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 38 (.branch 32 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (5)))))) (.branch 44 (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (6)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (7)) (.branch 49 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1876
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 22 (.leaf (13)) (.leaf (14)))))) (.branch 37 (.branch 31 (.branch 27 (.branch 26 (.leaf (15)) (.leaf (16))) (.branch 29 (.leaf (17)) (.leaf (18)))) (.branch 34 (.branch 32 (.leaf (19)) (.leaf (20))) (.branch 36 (.leaf (21)) (.leaf (22))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (23)) (.leaf (24))) (.branch 42 (.leaf (25)) (.leaf (26)))) (.branch 47 (.branch 46 (.leaf (27)) (.leaf (28))) (.branch 49 (.leaf (29)) (.leaf (30))))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 50 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-22))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.leaf (-4)) (.leaf (-3))),
  (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18))))) (.branch 36 (.branch 34 (.leaf (-17)) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_183_1877 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6))))) (.branch 22 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.leaf (7)) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 37 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (0)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (2)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (5)) (.branch 39 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (6)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (2)))) (.branch 48 (.leaf (7)) (.branch 49 (.leaf (0)) (.leaf (1))))))))
  code := certificateD8_1877
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))))) (.branch 36 (.branch 31 (.branch 26 (.leaf (13)) (.branch 29 (.leaf (14)) (.leaf (15)))) (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18))))) (.branch 42 (.branch 39 (.leaf (19)) (.branch 41 (.leaf (20)) (.leaf (21)))) (.branch 46 (.branch 44 (.leaf (22)) (.leaf (23))) (.branch 49 (.leaf (24)) (.leaf (25))))))),
  (.branch 25 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-22))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18))))) (.branch 36 (.branch 34 (.leaf (-17)) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_183_1878 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (5)) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 37 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (6))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (7)) (.leaf (0)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (3)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (4)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (0)) (.leaf (6)))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1878
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))))) (.branch 36 (.branch 31 (.branch 26 (.leaf (13)) (.branch 28 (.leaf (14)) (.leaf (15)))) (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18))))) (.branch 42 (.branch 38 (.leaf (19)) (.branch 41 (.leaf (20)) (.leaf (21)))) (.branch 46 (.branch 44 (.leaf (22)) (.leaf (23))) (.branch 48 (.leaf (24)) (.leaf (25))))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 45 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-41))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-29)) (.leaf (-31)))),
  (.branch 10 (.leaf (0)) (.branch 43 (.leaf (-20)) (.leaf (-21)))),
  (.branch 13 (.leaf (0)) (.leaf (-11))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 49 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 42 (.branch 38 (.branch 4 (.leaf (-41)) (.branch 21 (.leaf (-40)) (.leaf (-39)))) (.branch 40 (.branch 39 (.leaf (-36)) (.leaf (-33))) (.branch 41 (.leaf (-30)) (.leaf (-27))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-24)) (.leaf (-21))) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 44 (.branch 41 (.branch 24 (.leaf (-31)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-18)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-9))) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 31 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-1)) (.leaf (0)))]
def witnessD8_183_1879 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (6)) (.leaf (3)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))))) (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (4)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (4)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (0))))) (.branch 47 (.branch 45 (.leaf (1)) (.branch 46 (.leaf (7)) (.leaf (3)))) (.branch 48 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1879
  counts := ![(.branch 23 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 27 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.branch 34 (.leaf (12)) (.leaf (13))))) (.branch 42 (.branch 39 (.leaf (14)) (.leaf (15))) (.branch 44 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 49 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))) (.branch 27 (.leaf (-5)) (.branch 44 (.leaf (-6)) (.leaf (-7))))),
  (.branch 24 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-29))),
  (.branch 46 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 45 (.leaf (-7)) (.branch 49 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-3))) (.branch 46 (.leaf (-1)) (.leaf (0)))),
  (.branch 39 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 28 (.branch 24 (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27)))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.leaf (-23))))) (.branch 31 (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-17)) (.leaf (-16)))))) (.branch 42 (.branch 38 (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_183_1880 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (6)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (7)) (.leaf (0))) (.branch 49 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1880
  counts := ![(.branch 23 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 36 (.branch 28 (.branch 26 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14))))) (.branch 43 (.branch 38 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 46 (.leaf (18)) (.branch 48 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 44 (.leaf (8)) (.branch 50 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-43))),
  (.branch 17 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.leaf (-23))),
  (.branch 37 (.leaf (0)) (.leaf (-13))),
  (.branch 47 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 49 (.leaf (-4)) (.leaf (-2))),
  (.branch 46 (.leaf (-5)) (.leaf (-3))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-43)) (.leaf (-42))) (.branch 10 (.leaf (-41)) (.branch 11 (.leaf (-40)) (.leaf (-39))))) (.branch 14 (.branch 13 (.leaf (-38)) (.leaf (-37))) (.branch 15 (.leaf (-36)) (.branch 16 (.leaf (-35)) (.leaf (-34)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-33)) (.leaf (-32))) (.branch 20 (.leaf (-31)) (.branch 21 (.leaf (-30)) (.leaf (-29))))) (.branch 25 (.branch 23 (.leaf (-28)) (.branch 24 (.leaf (-27)) (.leaf (-26)))) (.branch 26 (.leaf (-25)) (.branch 27 (.leaf (-24)) (.leaf (-23))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18))))) (.branch 36 (.branch 34 (.leaf (-17)) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-33)) (.leaf (-32))) (.branch 20 (.leaf (-31)) (.leaf (-30)))) (.branch 23 (.branch 22 (.leaf (-29)) (.leaf (-28))) (.branch 24 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-23)) (.leaf (-22)))) (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.leaf (-18)))))) (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 39 (.branch 38 (.leaf (-13)) (.leaf (-12))) (.branch 40 (.leaf (-11)) (.leaf (-10))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 44 (.leaf (-7)) (.leaf (-6)))) (.branch 47 (.branch 46 (.leaf (-5)) (.leaf (-4))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 32 (.branch 29 (.branch 28 (.leaf (-23)) (.leaf (-22))) (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19))))) (.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-13)))))) (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_183_1881 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (7)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (5)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (6)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (6)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_1881
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 43 (.branch 40 (.leaf (15)) (.leaf (16))) (.branch 45 (.leaf (17)) (.branch 48 (.leaf (18)) (.leaf (19))))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 25 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-31))) (.branch 16 (.leaf (-43)) (.leaf (-46)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 20 (.branch 15 (.leaf (-28)) (.leaf (-29))) (.branch 25 (.leaf (-30)) (.leaf (-31))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-19)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-27)))),
  (.leaf (0)),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.branch 47 (.leaf (-5)) (.leaf (-23)))),
  (.branch 28 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 46 (.branch 17 (.leaf (-46)) (.leaf (-45))) (.branch 49 (.leaf (-38)) (.leaf (-19)))),
  (.branch 47 (.branch 26 (.leaf (-31)) (.leaf (-30))) (.branch 48 (.leaf (-25)) (.branch 49 (.leaf (-20)) (.leaf (-15))))),
  (.branch 46 (.branch 34 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 45 (.leaf (-23)) (.leaf (-20)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-14))) (.branch 49 (.leaf (-11)) (.leaf (-8))))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 44 (.leaf (-23)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-17)) (.leaf (-14))) (.branch 48 (.leaf (-11)) (.branch 49 (.leaf (-8)) (.leaf (-5)))))),
  (.leaf (0)),
  (.branch 35 (.leaf (-8)) (.leaf (-7))),
  (.branch 48 (.leaf (-23)) (.branch 49 (.leaf (-21)) (.leaf (-19)))),
  (.branch 39 (.branch 33 (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-21))) (.branch 31 (.leaf (-20)) (.branch 32 (.leaf (-19)) (.leaf (-18))))) (.branch 36 (.branch 34 (.leaf (-17)) (.branch 35 (.leaf (-16)) (.leaf (-15)))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_183_1882 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (0)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (6)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1882
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.leaf (15)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-41))),
  (.branch 19 (.leaf (0)) (.leaf (-31))),
  (.branch 29 (.leaf (0)) (.leaf (-21))),
  (.branch 39 (.leaf (0)) (.leaf (-11))),
  (.branch 49 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.leaf (-6)) (.leaf (-3))),
  (.branch 47 (.leaf (-2)) (.leaf (0))),
  (.branch 29 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-41)) (.leaf (-40))) (.branch 12 (.leaf (-39)) (.branch 13 (.leaf (-38)) (.leaf (-37))))) (.branch 16 (.branch 15 (.leaf (-36)) (.leaf (-35))) (.branch 17 (.leaf (-34)) (.branch 18 (.leaf (-33)) (.leaf (-32)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-31)) (.leaf (-30))) (.branch 22 (.leaf (-29)) (.branch 23 (.leaf (-28)) (.leaf (-27))))) (.branch 26 (.branch 25 (.leaf (-26)) (.leaf (-25))) (.branch 27 (.leaf (-24)) (.branch 28 (.leaf (-23)) (.leaf (-22))))))) (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 34 (.branch 26 (.branch 22 (.branch 20 (.leaf (-31)) (.branch 21 (.leaf (-30)) (.leaf (-29)))) (.branch 24 (.branch 23 (.leaf (-28)) (.leaf (-27))) (.branch 25 (.leaf (-26)) (.leaf (-25))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-24)) (.leaf (-23))) (.branch 29 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-17)))))) (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_183_1883 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (7)) (.leaf (1))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (6)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1883
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 40 (.leaf (14)) (.leaf (15))) (.branch 45 (.leaf (16)) (.branch 48 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 45 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 27 (.leaf (-13)) (.branch 30 (.leaf (-17)) (.leaf (-21))))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-5))) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-32)) (.leaf (-34)))),
  (.branch 14 (.leaf (0)) (.branch 47 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-14))),
  (.branch 24 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 46 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 43 (.branch 35 (.branch 31 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-12))) (.branch 49 (.leaf (-7)) (.leaf (-2))))),
  (.branch 45 (.branch 42 (.branch 29 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-14)) (.leaf (-12))))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.leaf (-5)) (.branch 49 (.leaf (-4)) (.leaf (-3))))),
  (.branch 44 (.branch 41 (.branch 23 (.leaf (-34)) (.branch 40 (.leaf (-33)) (.leaf (-30)))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_183_1884 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (5)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (2)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (7)) (.leaf (1))) (.branch 49 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1884
  counts := ![(.branch 24 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 46 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 8 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-17)))) (.branch 33 (.leaf (-21)) (.branch 36 (.leaf (-25)) (.leaf (-29))))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-16))),
  (.branch 22 (.leaf (0)) (.leaf (-28))),
  (.branch 47 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 44 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 47 (.leaf (-8)) (.leaf (-7)))),
  (.branch 41 (.branch 37 (.leaf (-29)) (.leaf (-28))) (.branch 45 (.leaf (-27)) (.branch 49 (.leaf (-26)) (.leaf (-21))))),
  (.branch 47 (.branch 29 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-14))) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 38 (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 29 (.branch 25 (.branch 23 (.leaf (-28)) (.branch 24 (.leaf (-27)) (.leaf (-26)))) (.branch 27 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-23)) (.leaf (-22))))) (.branch 32 (.branch 30 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-19)))) (.branch 34 (.branch 33 (.leaf (-18)) (.leaf (-17))) (.branch 35 (.leaf (-16)) (.leaf (-15)))))) (.branch 43 (.branch 39 (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))) (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_183_1885 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (5)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1885
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 36 (.leaf (-12)) (.leaf (-13)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.branch 49 (.leaf (-4)) (.leaf (-5))))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.branch 25 (.leaf (0)) (.leaf (-25))),
  (.leaf (0))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (-5)),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (-25)) (.branch 27 (.leaf (-24)) (.leaf (-23)))) (.branch 29 (.leaf (-22)) (.branch 30 (.leaf (-21)) (.leaf (-20))))) (.branch 34 (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17)))) (.branch 35 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-12)) (.leaf (-11)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-9)) (.leaf (-8))))) (.branch 46 (.branch 44 (.leaf (-7)) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_183_1886 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (7))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (6)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (4)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1886
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 36 (.leaf (-12)) (.leaf (-13)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 37 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 45 (.branch 43 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.leaf (-7)))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2)),
  (.branch 44 (.branch 41 (.branch 39 (.leaf (-12)) (.branch 40 (.leaf (-11)) (.leaf (-10)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_183_1887 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (6))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (5)) (.branch 33 (.leaf (7)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (4)) (.branch 42 (.leaf (6)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1887
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 14 (.leaf (-12)) (.branch 39 (.leaf (-14)) (.leaf (-15))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 40 (.leaf (-15)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 25 (.branch 8 (.leaf (-29)) (.leaf (-28))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 45 (.branch 26 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-21)) (.leaf (-18))))) (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-12))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-1)) (.leaf (0)))]
def witnessD8_183_1888 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (4))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (1)) (.leaf (0)))) (.branch 35 (.leaf (4)) (.branch 36 (.leaf (2)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (1)) (.leaf (0)))) (.branch 41 (.leaf (6)) (.branch 42 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (7)) (.leaf (4))))))))
  code := certificateD8_1888
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 40 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10)))),
  (.branch 25 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-4))))]
  high := ![(.branch 45 (.branch 41 (.leaf (-16)) (.leaf (-14))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 47 (.branch 40 (.leaf (-19)) (.leaf (-16))) (.branch 48 (.leaf (-12)) (.branch 49 (.leaf (-8)) (.leaf (-4))))),
  (.branch 47 (.branch 37 (.leaf (-17)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3))))),
  (.branch 39 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 48 (.leaf (-8)) (.branch 49 (.leaf (-6)) (.leaf (-4))))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-12)) (.leaf (-10)))) (.branch 48 (.branch 47 (.leaf (-8)) (.leaf (-6))) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 44 (.branch 25 (.branch 8 (.leaf (-29)) (.leaf (-28))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3)))]
def witnessD8_183_1889 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (5))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (7))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (5)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (6)) (.leaf (2)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (3)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (7))) (.branch 49 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_1889
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (-32)) (.leaf (-33)))),
  (.branch 14 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 45 (.leaf (-11)) (.leaf (-9))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 45 (.branch 43 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 44 (.leaf (-14)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 47 (.branch 46 (.leaf (-10)) (.leaf (-8))) (.branch 48 (.leaf (-6)) (.branch 49 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_183_1890 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.leaf (3))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.leaf (7)) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (4)) (.leaf (0)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (6)) (.leaf (1))))) (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (5)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1890
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.branch 47 (.leaf (-16)) (.leaf (-17))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.leaf (0)),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 36 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 44 (.leaf (-17)) (.branch 49 (.leaf (-12)) (.leaf (-6)))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 43 (.branch 39 (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-14)) (.leaf (-13)))) (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 46 (.branch 44 (.leaf (-8)) (.branch 45 (.leaf (-7)) (.leaf (-6)))) (.branch 48 (.branch 47 (.leaf (-5)) (.leaf (-4))) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2))))),
  (.branch 45 (.branch 43 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 44 (.leaf (-8)) (.leaf (-7)))) (.branch 47 (.branch 46 (.leaf (-6)) (.leaf (-5))) (.branch 48 (.leaf (-4)) (.branch 49 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD8_183_1891 : CycleWitness 8 where
  length := 50
  word := (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (3))))))) (.branch 37 (.branch 31 (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (6)) (.branch 30 (.leaf (0)) (.leaf (5))))) (.branch 34 (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2)))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (3)))))) (.branch 43 (.branch 40 (.branch 38 (.leaf (0)) (.branch 39 (.leaf (4)) (.leaf (2)))) (.branch 41 (.leaf (1)) (.branch 42 (.leaf (7)) (.leaf (0))))) (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (3)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1891
  counts := ![(.branch 22 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.branch 38 (.leaf (-19)) (.leaf (-20))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-11))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-2))) (.branch 37 (.leaf (-3)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (-32)) (.leaf (-33)))),
  (.branch 14 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 17 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 48 (.branch 39 (.leaf (-20)) (.leaf (-17))) (.branch 49 (.leaf (-12)) (.leaf (-7)))),
  (.branch 45 (.leaf (-11)) (.leaf (-9))),
  (.branch 48 (.branch 47 (.leaf (-16)) (.leaf (-12))) (.branch 49 (.leaf (-8)) (.leaf (-4)))),
  (.branch 47 (.branch 38 (.leaf (-5)) (.branch 46 (.leaf (-4)) (.leaf (-3)))) (.branch 48 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 41 (.branch 40 (.leaf (-33)) (.leaf (-30))) (.branch 42 (.leaf (-27)) (.branch 43 (.leaf (-24)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-18)) (.branch 46 (.leaf (-15)) (.leaf (-12)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 49 (.leaf (-6)) (.leaf (-3)))),
  (.branch 39 (.branch 34 (.branch 31 (.branch 30 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-17))))) (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-12)))))) (.branch 44 (.branch 41 (.branch 40 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-7))))) (.branch 47 (.branch 45 (.leaf (-6)) (.branch 46 (.leaf (-5)) (.leaf (-4)))) (.branch 48 (.leaf (-3)) (.branch 49 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 45 (.leaf (-6)) (.leaf (-5)))) (.branch 48 (.branch 47 (.leaf (-4)) (.leaf (-3))) (.branch 49 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_183 : Fin 19 → CycleWitness 8 := ![witnessD8_183_1873, witnessD8_183_1874, witnessD8_183_1875, witnessD8_183_1876, witnessD8_183_1877, witnessD8_183_1878, witnessD8_183_1879, witnessD8_183_1880, witnessD8_183_1881, witnessD8_183_1882, witnessD8_183_1883, witnessD8_183_1884, witnessD8_183_1885, witnessD8_183_1886, witnessD8_183_1887, witnessD8_183_1888, witnessD8_183_1889, witnessD8_183_1890, witnessD8_183_1891]
end RealPinwheel.FiveSixths


