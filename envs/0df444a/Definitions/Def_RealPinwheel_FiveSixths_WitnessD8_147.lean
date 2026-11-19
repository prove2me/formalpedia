-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_147
-- name    : RealPinwheel_FiveSixths_WitnessD8_147
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:06:44.688041+00:00
-- url     : https://prove2.me/theorems/ed3b7e6b-6e1a-4b67-b61f-0583a0b0cabd
-- title:
--   Exact witness block D8_147
-- statement:
--   These exact witnesses represent words 1262 through 1276 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1262–1276; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_147_1261 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (6)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (7)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_1261
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 44 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 56 (.leaf (-20)) (.leaf (-23)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 36 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-23)) (.leaf (-21))) (.branch 59 (.leaf (-19)) (.leaf (-17)))) (.branch 62 (.branch 61 (.leaf (-15)) (.leaf (-13))) (.branch 63 (.leaf (-11)) (.leaf (-9))))),
  (.branch 52 (.branch 37 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-6)))) (.branch 53 (.leaf (-4)) (.branch 54 (.leaf (-2)) (.leaf (0))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_147_1262 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1262
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-17)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-34)) (.leaf (-35)))),
  (.branch 42 (.branch 21 (.leaf (0)) (.leaf (-1))) (.branch 63 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 60 (.branch 48 (.leaf (-19)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 55 (.branch 32 (.leaf (-35)) (.branch 54 (.leaf (-33)) (.leaf (-30)))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessD8_147_1263 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (3)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (0))) (.branch 43 (.leaf (5)) (.leaf (7)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (7)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_1263
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-14)))) (.branch 35 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-15))) (.branch 56 (.leaf (-21)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.branch 43 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 62 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 63 (.leaf (-12)) (.leaf (-8)))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-26)) (.leaf (-24))) (.branch 59 (.leaf (-22)) (.leaf (-20)))) (.branch 62 (.branch 61 (.leaf (-18)) (.leaf (-16))) (.branch 63 (.leaf (-14)) (.leaf (-12))))),
  (.branch 60 (.branch 58 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 51 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_147_1264 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1264
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 63 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-28))),
  (.branch 20 (.leaf (0)) (.leaf (-44))),
  (.branch 52 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 59 (.leaf (-2)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-44)) (.leaf (-43))) (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40))))) (.branch 28 (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37)))) (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29))))) (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23))))))) (.branch 53 (.branch 47 (.branch 44 (.branch 43 (.leaf (-22)) (.leaf (-21))) (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18))))) (.branch 50 (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_147_1265 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (4)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (7)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (3))) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (7))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (3))) (.branch 63 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_1265
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-14)))) (.branch 35 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 37 (.leaf (-7)) (.branch 43 (.leaf (-9)) (.leaf (-11))))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-19)) (.leaf (-22)))),
  (.branch 36 (.branch 16 (.leaf (0)) (.leaf (-7))) (.branch 56 (.leaf (-10)) (.leaf (-13))))]
  high := ![(.branch 62 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 63 (.leaf (-12)) (.leaf (-8)))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 58 (.branch 44 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9)))) (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-3)) (.leaf (0))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.leaf (-5)) (.branch 53 (.leaf (-4)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 25 (.leaf (-22)) (.leaf (-21))) (.branch 50 (.leaf (-20)) (.leaf (-19)))) (.branch 53 (.branch 52 (.leaf (-18)) (.leaf (-17))) (.branch 54 (.leaf (-16)) (.leaf (-15))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.leaf (-11)))) (.branch 61 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-7)) (.leaf (-6))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-13)) (.leaf (-12))) (.branch 59 (.leaf (-11)) (.leaf (-10)))) (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))))]
def witnessD8_147_1266 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (3))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (7)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1266
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 60 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-36))),
  (.branch 60 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.leaf (-2)) (.leaf (-1))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28)))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-26))) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 43 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))))) (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_147_1267 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (6))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1267
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-56))),
  (.branch 40 (.leaf (0)) (.leaf (-24))),
  (.branch 56 (.leaf (0)) (.leaf (-8))),
  (.branch 24 (.leaf (0)) (.leaf (-40)))]
  high := ![(.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 54 (.leaf (-7)) (.leaf (-5))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 36 (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-56)) (.branch 10 (.leaf (-55)) (.leaf (-54)))) (.branch 13 (.branch 12 (.leaf (-53)) (.leaf (-52))) (.branch 14 (.leaf (-51)) (.leaf (-50))))) (.branch 18 (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 20 (.branch 19 (.leaf (-46)) (.leaf (-45))) (.branch 21 (.leaf (-44)) (.leaf (-43)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40)))) (.branch 27 (.branch 26 (.leaf (-39)) (.leaf (-38))) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 32 (.branch 30 (.leaf (-35)) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.leaf (-29))))))) (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 31 (.branch 30 (.leaf (-35)) (.leaf (-34))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))))) (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))))]
def witnessD8_147_1268 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (7))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (7)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_1268
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (-31)) (.leaf (-32)))),
  (.leaf (0))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 49 (.leaf (-16)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 58 (.branch 55 (.branch 33 (.leaf (-32)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD8_147_1269 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (5)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (3))) (.branch 39 (.leaf (7)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (4)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (5)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_1269
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 38 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 57 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 28 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-57))),
  (.branch 39 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 45 (.leaf (-4)) (.branch 58 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-57)) (.branch 9 (.leaf (-56)) (.leaf (-55)))) (.branch 12 (.branch 11 (.leaf (-54)) (.leaf (-53))) (.branch 13 (.leaf (-52)) (.leaf (-51))))) (.branch 17 (.branch 15 (.leaf (-50)) (.branch 16 (.leaf (-49)) (.leaf (-48)))) (.branch 19 (.branch 18 (.leaf (-47)) (.leaf (-46))) (.branch 20 (.leaf (-45)) (.leaf (-44)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41)))) (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.leaf (-37))))) (.branch 31 (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.leaf (-30))))))) (.branch 49 (.branch 42 (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.leaf (-23))))) (.branch 45 (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_147_1270 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (5))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (7))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (3)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_1270
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 64 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 21 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-5)) (.leaf (-6)))) (.branch 37 (.branch 34 (.leaf (-7)) (.leaf (-8))) (.branch 50 (.leaf (-9)) (.branch 53 (.leaf (-10)) (.leaf (-11)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-26))),
  (.branch 22 (.leaf (0)) (.leaf (-42))),
  (.branch 54 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 59 (.leaf (-14)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 61 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 62 (.leaf (-7)) (.branch 63 (.leaf (-4)) (.leaf (-1))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 51 (.branch 44 (.branch 41 (.branch 39 (.leaf (-26)) (.branch 40 (.leaf (-25)) (.leaf (-24)))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))) (.branch 47 (.branch 45 (.leaf (-20)) (.branch 46 (.leaf (-19)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (-42)) (.leaf (-41))) (.branch 25 (.leaf (-40)) (.branch 26 (.leaf (-39)) (.leaf (-38))))) (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.branch 31 (.leaf (-34)) (.leaf (-33)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.branch 36 (.leaf (-29)) (.leaf (-28))))) (.branch 40 (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))))) (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_147_1271 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (7)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (7)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (3)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (4))) (.branch 39 (.leaf (6)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (7)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (6)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (7)) (.leaf (4))))))))
  code := certificateD8_1271
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 48 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-49)) (.leaf (-52)))),
  (.branch 9 (.leaf (0)) (.branch 60 (.leaf (-19)) (.leaf (-20)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 44 (.leaf (-34)) (.leaf (-36)))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 53 (.leaf (-12)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 55 (.branch 29 (.leaf (-52)) (.branch 42 (.leaf (-51)) (.leaf (-50)))) (.branch 56 (.leaf (-45)) (.branch 57 (.leaf (-40)) (.leaf (-35))))) (.branch 61 (.branch 59 (.leaf (-30)) (.branch 60 (.leaf (-25)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 58 (.branch 45 (.leaf (-36)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_147_1272 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (4)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (4)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1272
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 64 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.branch 32 (.leaf (0)) (.leaf (-32))),
  (.leaf (0))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.leaf (-29)))) (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.leaf (-21)))) (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.leaf (-17)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_147_1273 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (7))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1273
  counts := ![(.branch 29 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 63 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-40))),
  (.branch 56 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 34 (.branch 29 (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 31 (.branch 30 (.leaf (-35)) (.leaf (-34))) (.branch 32 (.leaf (-33)) (.branch 33 (.leaf (-32)) (.leaf (-31)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (-30)) (.leaf (-29))) (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26))))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.branch 43 (.leaf (-22)) (.leaf (-21))))))) (.branch 54 (.branch 49 (.branch 46 (.branch 45 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16))))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_147_1274 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (5)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (7)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_1274
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 28 (.leaf (10)) (.leaf (11)))))) (.branch 47 (.branch 39 (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17))))) (.branch 55 (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20)))) (.branch 60 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 63 (.leaf (23)) (.leaf (24))))))),
  (.branch 30 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 54 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (-31))) (.branch 53 (.leaf (-32)) (.leaf (-33)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 58 (.leaf (-5)) (.branch 61 (.leaf (-4)) (.leaf (-3)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 60 (.branch 38 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_147_1275 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1275
  counts := ![(.branch 30 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 36 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 52 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 31 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 45 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 54 (.leaf (16)) (.leaf (17)))) (.branch 61 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 31 (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-5)) (.leaf (-6)))) (.branch 47 (.branch 34 (.leaf (-7)) (.leaf (-8))) (.branch 50 (.leaf (-9)) (.branch 63 (.leaf (-10)) (.leaf (-11)))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 24 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-56))),
  (.branch 40 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 56 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-11)),
  (.branch 61 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-56)) (.branch 10 (.leaf (-55)) (.leaf (-54)))) (.branch 13 (.branch 12 (.leaf (-53)) (.leaf (-52))) (.branch 14 (.leaf (-51)) (.leaf (-50))))) (.branch 18 (.branch 16 (.leaf (-49)) (.branch 17 (.leaf (-48)) (.leaf (-47)))) (.branch 20 (.branch 19 (.leaf (-46)) (.leaf (-45))) (.branch 21 (.leaf (-44)) (.leaf (-43)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-42)) (.branch 24 (.leaf (-41)) (.leaf (-40)))) (.branch 27 (.branch 26 (.leaf (-39)) (.leaf (-38))) (.branch 28 (.leaf (-37)) (.leaf (-36))))) (.branch 32 (.branch 30 (.leaf (-35)) (.branch 31 (.leaf (-34)) (.leaf (-33)))) (.branch 34 (.branch 33 (.leaf (-32)) (.leaf (-31))) (.branch 35 (.leaf (-30)) (.leaf (-29))))))) (.branch 50 (.branch 43 (.branch 39 (.branch 37 (.leaf (-28)) (.branch 38 (.leaf (-27)) (.leaf (-26)))) (.branch 41 (.branch 40 (.leaf (-25)) (.leaf (-24))) (.branch 42 (.leaf (-23)) (.leaf (-22))))) (.branch 46 (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19)))) (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))))) (.branch 57 (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22)))) (.branch 44 (.leaf (-21)) (.branch 45 (.leaf (-20)) (.leaf (-19))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))))) (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_147 : Fin 15 → CycleWitness 8 := ![witnessD8_147_1261, witnessD8_147_1262, witnessD8_147_1263, witnessD8_147_1264, witnessD8_147_1265, witnessD8_147_1266, witnessD8_147_1267, witnessD8_147_1268, witnessD8_147_1269, witnessD8_147_1270, witnessD8_147_1271, witnessD8_147_1272, witnessD8_147_1273, witnessD8_147_1274, witnessD8_147_1275]
end RealPinwheel.FiveSixths


