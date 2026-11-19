-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_162
-- name    : RealPinwheel_FiveSixths_WitnessD8_162
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:19:48.544844+00:00
-- url     : https://prove2.me/theorems/0f3cdb45-64a4-4f8c-b2b1-845190e24217
-- title:
--   Exact witness block D8_162
-- statement:
--   These exact witnesses represent words 1498 through 1514 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1498–1514; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_162_1497 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (5)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (4)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1497
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 33 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-10)))),
  (.branch 24 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-48))),
  (.branch 39 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 53 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 55 (.branch 49 (.leaf (-21)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.branch 52 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 35 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 56 (.branch 46 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 22 (.branch 16 (.branch 13 (.branch 11 (.leaf (-48)) (.branch 12 (.leaf (-47)) (.leaf (-46)))) (.branch 14 (.leaf (-45)) (.branch 15 (.leaf (-44)) (.leaf (-43))))) (.branch 19 (.branch 17 (.leaf (-42)) (.branch 18 (.leaf (-41)) (.leaf (-40)))) (.branch 20 (.leaf (-39)) (.branch 21 (.leaf (-38)) (.leaf (-37)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-36)) (.branch 24 (.leaf (-35)) (.leaf (-34)))) (.branch 26 (.leaf (-33)) (.branch 27 (.leaf (-32)) (.leaf (-31))))) (.branch 31 (.branch 29 (.leaf (-30)) (.branch 30 (.leaf (-29)) (.leaf (-28)))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-26)) (.leaf (-25))))))) (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_162_1498 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (4))) (.branch 35 (.leaf (7)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (5)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (2))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (0))) (.branch 53 (.leaf (7)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (0))) (.branch 57 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_1498
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 34 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-13)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 39 (.leaf (-27)) (.leaf (-32)))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (-14)) (.leaf (-16)))),
  (.branch 35 (.branch 16 (.leaf (0)) (.leaf (-4))) (.branch 53 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 53 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 56 (.branch 41 (.leaf (-14)) (.leaf (-12))) (.branch 57 (.leaf (-8)) (.leaf (-4)))),
  (.branch 54 (.branch 52 (.branch 40 (.leaf (-32)) (.leaf (-31))) (.branch 53 (.leaf (-27)) (.leaf (-23)))) (.branch 56 (.branch 55 (.leaf (-19)) (.leaf (-15))) (.branch 57 (.leaf (-11)) (.leaf (-7))))),
  (.branch 23 (.branch 11 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (0))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 51 (.branch 47 (.branch 25 (.leaf (-16)) (.branch 46 (.leaf (-15)) (.leaf (-14)))) (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 54 (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))))]
def witnessD8_162_1499 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (5))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (6)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (4)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (3))) (.branch 49 (.leaf (0)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1499
  counts := ![(.branch 27 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))) (.branch 43 (.branch 35 (.branch 30 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13)))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))) (.branch 51 (.branch 46 (.leaf (17)) (.branch 49 (.leaf (18)) (.leaf (19)))) (.branch 53 (.leaf (20)) (.branch 56 (.leaf (21)) (.leaf (22))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 24 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 8 (.leaf (-10)) (.leaf (-12)))) (.branch 37 (.branch 32 (.leaf (-14)) (.leaf (-15))) (.branch 53 (.leaf (-17)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 39 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-17)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-6)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 54 (.leaf (-19)) (.branch 57 (.leaf (-18)) (.leaf (-14)))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 55 (.branch 40 (.leaf (-15)) (.leaf (-14))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 39 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0)))),
  (.branch 50 (.branch 46 (.branch 24 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-15)))) (.branch 48 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_162_1500 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (5))) (.branch 35 (.leaf (0)) (.leaf (7))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (4)) (.leaf (3)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (6)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (1))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (7)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_1500
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 16 (.leaf (-22)) (.branch 23 (.leaf (-23)) (.leaf (-24))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 18 (.leaf (-14)) (.branch 25 (.leaf (-15)) (.leaf (-16))))),
  (.branch 14 (.leaf (0)) (.branch 43 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-37)) (.leaf (-38)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (-7))) (.branch 55 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 57 (.leaf (-4)) (.leaf (-3))),
  (.branch 55 (.branch 53 (.leaf (-24)) (.branch 54 (.leaf (-20)) (.leaf (-16)))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 56 (.branch 55 (.leaf (-16)) (.leaf (-12))) (.branch 57 (.leaf (-8)) (.leaf (-4)))),
  (.branch 44 (.leaf (-3)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 50 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 48 (.branch 27 (.leaf (-38)) (.branch 47 (.leaf (-36)) (.leaf (-33)))) (.branch 49 (.leaf (-30)) (.branch 50 (.leaf (-27)) (.leaf (-24))))) (.branch 54 (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_162_1501 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (7))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (7))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_1501
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-3)))) (.branch 42 (.leaf (-4)) (.branch 57 (.leaf (-6)) (.leaf (-7))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-19)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.leaf (-7)),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 47 (.branch 24 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-15))) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 55 (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))))]
def witnessD8_162_1502 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (7))) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (5)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (6)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (3))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (4)) (.leaf (7))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_1502
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-16)) (.leaf (-19)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (-5))) (.branch 52 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.branch 49 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 52 (.branch 37 (.leaf (-15)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 43 (.leaf (-3)) (.leaf (-2))),
  (.branch 51 (.branch 47 (.branch 24 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.branch 48 (.leaf (-16)) (.leaf (-15))) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 55 (.branch 53 (.leaf (-11)) (.branch 54 (.leaf (-10)) (.leaf (-9)))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))))]
def witnessD8_162_1503 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (6))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (7)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (6))) (.branch 35 (.leaf (5)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (4))) (.branch 42 (.leaf (2)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (7)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (3)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (2))) (.branch 53 (.leaf (4)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (3))) (.branch 57 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1503
  counts := ![(.branch 25 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 53 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 17 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-5)) (.leaf (-6)))) (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 56 (.leaf (-9)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-28)) (.leaf (-29)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 51 (.branch 41 (.leaf (-21)) (.branch 46 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 57 (.leaf (-14)) (.leaf (-12))),
  (.branch 54 (.branch 30 (.leaf (-29)) (.branch 42 (.leaf (-27)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-3))]
def witnessD8_162_1504 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (3)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (7)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (6))) (.branch 28 (.leaf (5)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (2)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (7)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (2))) (.branch 42 (.leaf (3)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (4))) (.branch 49 (.leaf (6)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (2)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (7))) (.branch 57 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1504
  counts := ![(.branch 25 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-5)) (.leaf (-6)))) (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (-12)) (.leaf (-15)))),
  (.branch 38 (.branch 20 (.leaf (0)) (.leaf (-1))) (.branch 56 (.leaf (-4)) (.leaf (-7))))]
  high := ![(.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 51 (.branch 41 (.leaf (-21)) (.branch 46 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (0)),
  (.branch 54 (.branch 43 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-3)),
  (.branch 53 (.branch 50 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-9))) (.branch 56 (.leaf (-8)) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 57 (.leaf (-7)) (.leaf (-6)))]
def witnessD8_162_1505 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (1)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (4)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (7))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (1)) (.leaf (4)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (3))) (.branch 57 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1505
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 28 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.branch 57 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.branch 52 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 19 (.leaf (0)) (.leaf (-39))),
  (.branch 48 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 46 (.leaf (-8)) (.leaf (-7))) (.branch 54 (.leaf (-6)) (.leaf (-5)))),
  (.branch 44 (.leaf (-2)) (.leaf (0))),
  (.branch 47 (.leaf (-7)) (.branch 57 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.branch 39 (.branch 36 (.branch 34 (.leaf (-25)) (.branch 35 (.leaf (-24)) (.leaf (-23)))) (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20))))) (.branch 42 (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17)))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-15)) (.leaf (-14)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))) (.branch 49 (.leaf (-10)) (.branch 50 (.leaf (-9)) (.leaf (-8))))) (.branch 54 (.branch 52 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-39)) (.leaf (-38))) (.branch 22 (.leaf (-37)) (.leaf (-36)))) (.branch 25 (.branch 24 (.leaf (-35)) (.leaf (-34))) (.branch 26 (.leaf (-33)) (.branch 27 (.leaf (-32)) (.leaf (-31)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-30)) (.leaf (-29))) (.branch 31 (.leaf (-28)) (.branch 32 (.leaf (-27)) (.leaf (-26))))) (.branch 35 (.branch 34 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.branch 37 (.leaf (-22)) (.leaf (-21))))))) (.branch 48 (.branch 43 (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-19))) (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16))))) (.branch 45 (.branch 44 (.leaf (-15)) (.leaf (-14))) (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))))) (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 51 (.leaf (-8)) (.branch 52 (.leaf (-7)) (.leaf (-6))))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_162_1506 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (7))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (6))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 41 (.branch 40 (.leaf (4)) (.leaf (0))) (.branch 42 (.leaf (2)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (5)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (6))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (2)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (4)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1506
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-3)))) (.branch 42 (.leaf (-4)) (.branch 57 (.leaf (-6)) (.leaf (-7))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 52 (.leaf (-17)) (.leaf (-22)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 46 (.leaf (-13)) (.leaf (-14)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-7)),
  (.branch 55 (.branch 53 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-18)))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.branch 49 (.branch 47 (.leaf (-14)) (.branch 48 (.leaf (-13)) (.leaf (-12)))) (.branch 50 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0)))]
def witnessD8_162_1507 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (7)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (7)) (.leaf (4))) (.branch 35 (.leaf (2)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (2))) (.branch 42 (.leaf (6)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (5)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (4))) (.branch 49 (.leaf (3)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (7))) (.branch 53 (.leaf (2)) (.leaf (0)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (3))) (.branch 57 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1507
  counts := ![(.branch 25 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-5)) (.leaf (-6)))) (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-8))) (.branch 46 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 56 (.leaf (-9)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 28 (.leaf (0)) (.branch 57 (.leaf (-2)) (.leaf (-3)))),
  (.branch 23 (.branch 4 (.leaf (0)) (.leaf (-46))) (.branch 42 (.leaf (-47)) (.leaf (-48)))),
  (.branch 13 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 51 (.branch 41 (.leaf (-21)) (.branch 46 (.leaf (-20)) (.leaf (-19)))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (0)),
  (.branch 57 (.leaf (-14)) (.leaf (-12))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-3)),
  (.branch 50 (.branch 46 (.branch 44 (.branch 43 (.leaf (-48)) (.leaf (-45))) (.branch 45 (.leaf (-42)) (.leaf (-39)))) (.branch 48 (.branch 47 (.leaf (-36)) (.leaf (-33))) (.branch 49 (.leaf (-30)) (.leaf (-27))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-24)) (.leaf (-21))) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 54 (.branch 14 (.leaf (-19)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_162_1508 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (7)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (5)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (1))) (.branch 57 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1508
  counts := ![(.branch 28 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 33 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 48 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 57 (.leaf (19)) (.leaf (20))))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-14)) (.leaf (-17)))),
  (.branch 29 (.leaf (0)) (.leaf (-2))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-10))) (.branch 47 (.leaf (-12)) (.leaf (-13)))),
  (.branch 25 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-47))),
  (.branch 40 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 54 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.branch 32 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 47 (.leaf (-14)) (.leaf (-13))) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 50 (.branch 44 (.leaf (-17)) (.leaf (-16))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 30 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 50 (.leaf (-11)) (.branch 51 (.leaf (-10)) (.leaf (-9))))) (.branch 55 (.branch 53 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-47)) (.leaf (-46))) (.branch 14 (.leaf (-45)) (.branch 15 (.leaf (-44)) (.leaf (-43))))) (.branch 19 (.branch 17 (.leaf (-42)) (.branch 18 (.leaf (-41)) (.leaf (-40)))) (.branch 20 (.leaf (-39)) (.branch 21 (.leaf (-38)) (.leaf (-37)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-36)) (.branch 24 (.leaf (-35)) (.leaf (-34)))) (.branch 26 (.leaf (-33)) (.branch 27 (.leaf (-32)) (.leaf (-31))))) (.branch 31 (.branch 29 (.leaf (-30)) (.branch 30 (.leaf (-29)) (.leaf (-28)))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-26)) (.leaf (-25))))))) (.branch 46 (.branch 40 (.branch 37 (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 38 (.leaf (-21)) (.branch 39 (.leaf (-20)) (.leaf (-19))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))))) (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 44 (.branch 42 (.branch 41 (.leaf (-18)) (.leaf (-17))) (.branch 43 (.leaf (-16)) (.leaf (-15)))) (.branch 46 (.branch 45 (.leaf (-14)) (.leaf (-13))) (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-9)) (.leaf (-8))) (.branch 52 (.leaf (-7)) (.leaf (-6)))) (.branch 55 (.branch 54 (.leaf (-5)) (.leaf (-4))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_162_1509 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (0))) (.branch 42 (.leaf (1)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (3)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (5)) (.leaf (4))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_1509
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 58 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 32 (.leaf (-31)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.branch 48 (.leaf (-23)) (.leaf (-24)))),
  (.branch 3 (.leaf (0)) (.branch 31 (.leaf (-9)) (.leaf (-13)))),
  (.branch 33 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 40 (.leaf (-2)) (.leaf (-5)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 23 (.leaf (-14)) (.branch 52 (.leaf (-17)) (.leaf (-22))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (-10))) (.branch 51 (.leaf (-12)) (.leaf (-13)))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-36)) (.leaf (-35))) (.branch 39 (.leaf (-34)) (.branch 42 (.leaf (-33)) (.leaf (-32))))) (.branch 51 (.branch 48 (.leaf (-31)) (.leaf (-30))) (.branch 54 (.leaf (-29)) (.branch 57 (.leaf (-28)) (.leaf (-16)))))),
  (.branch 56 (.branch 49 (.leaf (-24)) (.leaf (-22))) (.branch 57 (.leaf (-17)) (.leaf (-12)))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.leaf (-5)),
  (.branch 55 (.branch 53 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-18)))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.leaf (-7))))),
  (.branch 50 (.branch 46 (.branch 44 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 48 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 49 (.leaf (-10)) (.leaf (-9))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-8)) (.leaf (-7))) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.leaf (-1)) (.leaf (0)))]
def witnessD8_162_1510 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (4))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (7))) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (4)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (3)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (6)) (.branch 45 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (3)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (5))) (.branch 53 (.leaf (2)) (.leaf (7)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1510
  counts := ![(.branch 27 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 33 (.branch 30 (.leaf (7)) (.leaf (8))) (.branch 38 (.leaf (9)) (.leaf (10)))) (.branch 51 (.branch 47 (.leaf (11)) (.leaf (12))) (.branch 56 (.leaf (13)) (.leaf (14)))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 30 (.leaf (-24)) (.branch 33 (.leaf (-26)) (.leaf (-33))))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.branch 24 (.leaf (-19)) (.leaf (-20))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 49 (.leaf (-6)) (.leaf (-7)))),
  (.branch 19 (.leaf (0)) (.branch 48 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-43))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 43 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 52 (.leaf (-31)) (.branch 57 (.leaf (-28)) (.leaf (-23))))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-16))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 50 (.leaf (-7)) (.leaf (-5))),
  (.branch 49 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 38 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 46 (.branch 6 (.leaf (-43)) (.branch 45 (.leaf (-42)) (.leaf (-39)))) (.branch 48 (.branch 47 (.leaf (-36)) (.leaf (-33))) (.branch 49 (.leaf (-30)) (.leaf (-27))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (-24)) (.leaf (-21))) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 35 (.leaf (-14)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_162_1511 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (6))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (0))) (.branch 35 (.leaf (5)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (7)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (3)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (4)) (.leaf (0))) (.branch 49 (.leaf (5)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (6)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_1511
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 44 (.leaf (-25)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (-10)) (.leaf (-13)))),
  (.branch 40 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 49 (.branch 45 (.leaf (-30)) (.leaf (-28))) (.branch 53 (.leaf (-26)) (.branch 57 (.leaf (-24)) (.leaf (-17))))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.branch 55 (.branch 47 (.leaf (-19)) (.leaf (-16))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 54 (.branch 34 (.leaf (-17)) (.branch 44 (.leaf (-16)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3))))),
  (.branch 38 (.leaf (-5)) (.branch 48 (.leaf (-4)) (.leaf (-3)))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-18)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 54 (.branch 52 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))]
def witnessD8_162_1512 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (6)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (3))) (.branch 35 (.leaf (7)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (0)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (6)) (.branch 45 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (4))) (.branch 49 (.leaf (1)) (.leaf (2))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (5))) (.branch 53 (.leaf (0)) (.leaf (7)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (4))) (.branch 57 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_1512
  counts := ![(.branch 24 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 32 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 57 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (-11)) (.leaf (-12)))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (-40))) (.branch 44 (.leaf (-41)) (.leaf (-42)))),
  (.branch 15 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 55 (.branch 48 (.leaf (-26)) (.branch 54 (.leaf (-25)) (.leaf (-20)))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 51 (.leaf (-4)) (.leaf (-3))),
  (.branch 53 (.branch 52 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 49 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-10)) (.leaf (-8)))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 47 (.branch 45 (.leaf (-42)) (.branch 46 (.leaf (-39)) (.leaf (-36)))) (.branch 49 (.branch 48 (.leaf (-33)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.leaf (-24))))) (.branch 54 (.branch 52 (.leaf (-21)) (.branch 53 (.leaf (-18)) (.leaf (-15)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-9))) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_162_1513 : CycleWitness 8 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (0))) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (1)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (7)))) (.branch 48 (.branch 47 (.leaf (3)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (4)))) (.branch 56 (.branch 55 (.leaf (2)) (.leaf (1))) (.branch 57 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1513
  counts := ![(.branch 28 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 44 (.branch 34 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.branch 40 (.leaf (12)) (.leaf (13))))) (.branch 50 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 53 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 32 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 24 (.branch 11 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 21 (.leaf (-6)) (.leaf (-7)))) (.branch 40 (.branch 30 (.leaf (-8)) (.leaf (-10))) (.branch 50 (.leaf (-11)) (.branch 53 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 45 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-18)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 17 (.leaf (0)) (.leaf (-41))),
  (.branch 46 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 54 (.leaf (-13)) (.leaf (-12))),
  (.branch 46 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 50 (.branch 38 (.leaf (-18)) (.branch 44 (.leaf (-17)) (.leaf (-16)))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 55 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 45 (.branch 39 (.branch 36 (.branch 34 (.leaf (-25)) (.branch 35 (.leaf (-24)) (.leaf (-23)))) (.branch 37 (.leaf (-22)) (.branch 38 (.leaf (-21)) (.leaf (-20))))) (.branch 42 (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17)))) (.branch 43 (.leaf (-16)) (.branch 44 (.leaf (-15)) (.leaf (-14)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-13)) (.branch 47 (.leaf (-12)) (.leaf (-11)))) (.branch 49 (.leaf (-10)) (.branch 50 (.leaf (-9)) (.leaf (-8))))) (.branch 54 (.branch 52 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5)))) (.branch 56 (.branch 55 (.leaf (-4)) (.leaf (-3))) (.branch 57 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 27 (.branch 22 (.branch 19 (.branch 18 (.leaf (-41)) (.leaf (-40))) (.branch 20 (.leaf (-39)) (.branch 21 (.leaf (-38)) (.leaf (-37))))) (.branch 24 (.branch 23 (.leaf (-36)) (.leaf (-35))) (.branch 25 (.leaf (-34)) (.branch 26 (.leaf (-33)) (.leaf (-32)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-31)) (.leaf (-30))) (.branch 30 (.leaf (-29)) (.branch 31 (.leaf (-28)) (.leaf (-27))))) (.branch 34 (.branch 33 (.leaf (-26)) (.leaf (-25))) (.branch 35 (.leaf (-24)) (.branch 36 (.leaf (-23)) (.leaf (-22))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-21)) (.leaf (-20))) (.branch 40 (.leaf (-19)) (.branch 41 (.leaf (-18)) (.leaf (-17))))) (.branch 44 (.branch 43 (.leaf (-16)) (.leaf (-15))) (.branch 45 (.leaf (-14)) (.branch 46 (.leaf (-13)) (.leaf (-12)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-11)) (.leaf (-10))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 49 (.branch 47 (.leaf (-12)) (.branch 48 (.leaf (-11)) (.leaf (-10)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-7))))) (.branch 55 (.branch 53 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))) (.branch 56 (.leaf (-3)) (.branch 57 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_162 : Fin 17 → CycleWitness 8 := ![witnessD8_162_1497, witnessD8_162_1498, witnessD8_162_1499, witnessD8_162_1500, witnessD8_162_1501, witnessD8_162_1502, witnessD8_162_1503, witnessD8_162_1504, witnessD8_162_1505, witnessD8_162_1506, witnessD8_162_1507, witnessD8_162_1508, witnessD8_162_1509, witnessD8_162_1510, witnessD8_162_1511, witnessD8_162_1512, witnessD8_162_1513]
end RealPinwheel.FiveSixths


