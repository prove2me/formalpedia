-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_150
-- name    : RealPinwheel_FiveSixths_WitnessD8_150
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:08:26.509195+00:00
-- url     : https://prove2.me/theorems/d0a2a51c-f372-41b6-97ea-1911710e7cda
-- title:
--   Exact witness block D8_150
-- statement:
--   These exact witnesses represent words 1307 through 1321 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1307–1321; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_150_1306 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (7)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (2))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (7)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1306
  counts := ![(.branch 28 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 41 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 50 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 32 (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 38 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))) (.branch 41 (.branch 18 (.leaf (-15)) (.leaf (-16))) (.branch 50 (.leaf (-17)) (.leaf (-18))))),
  (.branch 25 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 34 (.leaf (-9)) (.branch 57 (.leaf (-10)) (.leaf (-11))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 42 (.leaf (-3)) (.branch 58 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-23)) (.leaf (-25)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-40)) (.leaf (-41)))),
  (.branch 40 (.branch 19 (.leaf (0)) (.leaf (-7))) (.branch 61 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 61 (.branch 51 (.leaf (-18)) (.branch 56 (.leaf (-17)) (.leaf (-16)))) (.branch 62 (.leaf (-13)) (.branch 63 (.leaf (-10)) (.leaf (-7))))),
  (.branch 58 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-7)))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-3))) (.branch 61 (.leaf (-1)) (.leaf (0)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 59 (.branch 57 (.branch 46 (.leaf (-25)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-1)),
  (.branch 57 (.branch 53 (.branch 30 (.leaf (-41)) (.branch 52 (.leaf (-39)) (.leaf (-36)))) (.branch 55 (.branch 54 (.leaf (-33)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_150_1307 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (7)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (6))) (.branch 39 (.leaf (0)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (7)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (6)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (3)) (.leaf (0))) (.branch 63 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_1307
  counts := ![(.branch 30 (.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 43 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 59 (.leaf (18)) (.branch 62 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 40 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 54 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 47 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 51 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (-9)) (.leaf (-11)))) (.branch 39 (.leaf (-12)) (.branch 55 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-49)) (.leaf (-53)))),
  (.branch 9 (.leaf (0)) (.branch 47 (.leaf (-19)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.branch 63 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-34)) (.leaf (-37))))]
  high := ![(.branch 56 (.leaf (-14)) (.branch 63 (.leaf (-12)) (.leaf (-8)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 42 (.branch 16 (.leaf (-53)) (.branch 29 (.leaf (-52)) (.leaf (-51)))) (.branch 55 (.leaf (-50)) (.branch 56 (.leaf (-45)) (.leaf (-40))))) (.branch 60 (.branch 58 (.leaf (-35)) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 61 (.branch 48 (.leaf (-21)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 59 (.branch 45 (.branch 32 (.leaf (-37)) (.leaf (-36))) (.branch 58 (.leaf (-35)) (.leaf (-30)))) (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))))]
def witnessD8_150_1308 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (6))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (4)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (3))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (4)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (6)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (5))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (4)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (4))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (7)) (.leaf (3))) (.branch 63 (.leaf (2)) (.leaf (6))))))))
  code := certificateD8_1308
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 31 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 37 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 30 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 36 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 27 (.leaf (-24)) (.leaf (-25)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-9)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 41 (.leaf (-13)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 32 (.branch 7 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-8)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 60 (.leaf (-25)) (.leaf (-20))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 44 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5)))),
  (.branch 49 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 56 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-11))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_150_1309 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (3))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (2)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (7)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (6))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (7)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (4)))) (.branch 62 (.branch 61 (.leaf (7)) (.leaf (2))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1309
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-46))) (.branch 16 (.leaf (-47)) (.branch 23 (.leaf (-48)) (.leaf (-49))))) (.branch 44 (.branch 37 (.leaf (-50)) (.leaf (-51))) (.branch 51 (.leaf (-52)) (.branch 58 (.leaf (-53)) (.leaf (-54)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.branch 26 (.leaf (-21)) (.leaf (-22))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))) (.branch 35 (.branch 28 (.leaf (-3)) (.leaf (-4))) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-37)) (.leaf (-38)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 56 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 40 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 59 (.leaf (-54)) (.branch 60 (.leaf (-45)) (.leaf (-36)))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 27 (.leaf (-22)) (.branch 63 (.leaf (-18)) (.leaf (-9)))),
  (.branch 43 (.leaf (-6)) (.leaf (0))),
  (.branch 61 (.branch 11 (.leaf (-38)) (.leaf (-36))) (.branch 62 (.leaf (-27)) (.branch 63 (.leaf (-18)) (.leaf (-9))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 41 (.leaf (-4)) (.leaf (-3))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_150_1310 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (6))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (3))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (6))) (.branch 43 (.leaf (3)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (3)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (7))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (5))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (2))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1310
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 59 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 57 (.leaf (7)) (.branch 64 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 22 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))) (.branch 38 (.leaf (-11)) (.branch 54 (.leaf (-12)) (.leaf (-13))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-41))) (.branch 16 (.leaf (-42)) (.leaf (-43)))) (.branch 37 (.branch 30 (.leaf (-44)) (.leaf (-45))) (.branch 51 (.leaf (-46)) (.leaf (-48))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-17)) (.leaf (-19)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))) (.branch 35 (.leaf (-3)) (.branch 49 (.leaf (-5)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-25)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 61 (.branch 55 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-10)) (.branch 63 (.leaf (-8)) (.leaf (-6))))),
  (.branch 61 (.branch 52 (.leaf (-48)) (.branch 60 (.leaf (-41)) (.leaf (-33)))) (.branch 62 (.leaf (-25)) (.branch 63 (.leaf (-17)) (.leaf (-9))))),
  (.branch 20 (.leaf (-19)) (.branch 63 (.leaf (-17)) (.leaf (-9)))),
  (.branch 50 (.leaf (-7)) (.branch 58 (.leaf (-2)) (.leaf (0)))),
  (.branch 54 (.branch 18 (.leaf (-27)) (.leaf (-26))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-15)) (.leaf (-9))))),
  (.branch 60 (.branch 48 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_150_1311 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (7)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (4)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1311
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 56 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 60 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 54 (.branch 10 (.leaf (-37)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-5)) (.leaf (-3)))]
def witnessD8_150_1312 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (4)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (5))) (.branch 39 (.leaf (1)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (7))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_1312
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))) (.branch 46 (.branch 37 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 55 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 30 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 39 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 54 (.leaf (8)) (.branch 61 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 57 (.leaf (4)) (.leaf (5))))),
  (.branch 38 (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 14 (.leaf (-29)) (.branch 23 (.leaf (-30)) (.leaf (-31))))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 34 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 25 (.leaf (0)) (.branch 50 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 61 (.branch 56 (.leaf (-31)) (.leaf (-28))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 40 (.leaf (-15)) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 55 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-6)) (.leaf (-4))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.leaf (-8)) (.branch 59 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.branch 61 (.leaf (-5)) (.leaf (-4))) (.branch 63 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_150_1313 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (5))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (3)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (5))) (.branch 47 (.leaf (0)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (1))) (.branch 59 (.leaf (3)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (5))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1313
  counts := ![(.branch 28 (.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (7)) (.leaf (8))) (.branch 42 (.leaf (9)) (.leaf (10)))) (.branch 56 (.branch 51 (.leaf (11)) (.leaf (12))) (.branch 60 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-26)) (.branch 28 (.leaf (-27)) (.leaf (-28))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-17)) (.leaf (-19)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 45 (.leaf (-12)) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 54 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0)))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3)))))]
def witnessD8_150_1314 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (5))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (3))) (.branch 51 (.leaf (1)) (.leaf (5)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (1))) (.branch 63 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_1314
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 50 (.branch 36 (.leaf (5)) (.branch 44 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 24 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 36 (.leaf (-4)) (.branch 56 (.leaf (-6)) (.leaf (-7))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-5)))) (.branch 45 (.leaf (-7)) (.branch 61 (.leaf (-9)) (.leaf (-11))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-49)) (.leaf (-50)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-16))) (.branch 58 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.branch 61 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9)))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 27 (.leaf (-50)) (.leaf (-48))) (.branch 50 (.leaf (-45)) (.leaf (-42)))) (.branch 53 (.branch 52 (.leaf (-39)) (.leaf (-36))) (.branch 54 (.leaf (-33)) (.leaf (-30))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-27)) (.leaf (-24))) (.branch 58 (.leaf (-21)) (.leaf (-18)))) (.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))))),
  (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_150_1315 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (7))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (7))) (.branch 43 (.leaf (0)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (4)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (7))) (.branch 59 (.leaf (0)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (1))) (.branch 63 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1315
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 56 (.leaf (-39)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-4)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 56 (.leaf (-1)) (.leaf (0))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-40)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 38 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_150_1316 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (5))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (3)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (3)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (7)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (5))) (.branch 47 (.leaf (4)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (3)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (5))) (.branch 63 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_1316
  counts := ![(.branch 27 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 59 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 28 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 12 (.leaf (-5)) (.branch 23 (.leaf (-6)) (.leaf (-7))))) (.branch 44 (.branch 39 (.leaf (-8)) (.leaf (-9))) (.branch 55 (.leaf (-10)) (.branch 60 (.leaf (-11)) (.leaf (-12)))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 61 (.branch 60 (.leaf (-15)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 59 (.leaf (-2)) (.leaf (0))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-11))) (.branch 63 (.leaf (-10)) (.leaf (-9)))),
  (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 57 (.branch 54 (.branch 10 (.leaf (-37)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-5)) (.leaf (-3)))]
def witnessD8_150_1317 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (6))) (.branch 23 (.leaf (0)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (2))) (.branch 31 (.leaf (1)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (4))) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (3))) (.branch 39 (.leaf (0)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (1))) (.branch 43 (.leaf (4)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (5)) (.leaf (2))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (1)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (5))) (.branch 55 (.leaf (0)) (.leaf (7))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (1))) (.branch 59 (.leaf (6)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (4)) (.leaf (2))) (.branch 63 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_1317
  counts := ![(.branch 28 (.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 57 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 52 (.branch 43 (.leaf (4)) (.leaf (5))) (.branch 61 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 45 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 32 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-5)) (.branch 51 (.leaf (-7)) (.leaf (-9))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 20 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-50)) (.leaf (-51)))) (.branch 29 (.leaf (-52)) (.branch 38 (.leaf (-53)) (.leaf (-54))))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))) (.branch 45 (.branch 36 (.leaf (-3)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-36))) (.branch 22 (.leaf (-37)) (.leaf (-38)))),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 61 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-9)),
  (.branch 54 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 58 (.branch 39 (.leaf (-54)) (.leaf (-49))) (.branch 59 (.leaf (-42)) (.leaf (-35)))) (.branch 62 (.branch 61 (.leaf (-28)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 62 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 63 (.leaf (-14)) (.leaf (-7)))),
  (.branch 55 (.leaf (-6)) (.leaf (0))),
  (.branch 61 (.branch 23 (.leaf (-38)) (.branch 60 (.leaf (-35)) (.leaf (-28)))) (.branch 62 (.leaf (-21)) (.branch 63 (.leaf (-14)) (.leaf (-7))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_150_1318 : CycleWitness 8 where
  length := 63
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (3))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (4)))) (.branch 29 (.branch 28 (.leaf (3)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (0))))))) (.branch 47 (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (4)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (0)) (.leaf (6))) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (0)))))) (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (4)) (.leaf (3))) (.branch 50 (.leaf (0)) (.leaf (1)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 54 (.leaf (0)) (.leaf (4))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (3)) (.leaf (0))) (.branch 58 (.leaf (1)) (.leaf (0)))) (.branch 61 (.branch 60 (.leaf (2)) (.leaf (0))) (.branch 62 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1318
  counts := ![(.branch 31 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))) (.branch 26 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.leaf (13)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16)))) (.branch 43 (.branch 40 (.leaf (17)) (.leaf (18))) (.branch 45 (.leaf (19)) (.leaf (20))))) (.branch 54 (.branch 50 (.leaf (21)) (.branch 52 (.leaf (22)) (.leaf (23)))) (.branch 59 (.branch 57 (.leaf (24)) (.leaf (25))) (.branch 61 (.leaf (26)) (.leaf (27))))))),
  (.branch 30 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 58 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 42 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 62 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-13)) (.branch 55 (.leaf (-18)) (.leaf (-23))))),
  (.branch 20 (.leaf (0)) (.leaf (-43))),
  (.branch 41 (.leaf (0)) (.leaf (-22))),
  (.branch 62 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 62 (.leaf (-6)) (.leaf (-3))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1))))),
  (.branch 61 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-23)) (.leaf (-22))) (.branch 58 (.leaf (-21)) (.leaf (-20)))) (.branch 61 (.branch 60 (.leaf (-19)) (.leaf (-18))) (.branch 62 (.leaf (-17)) (.leaf (-16))))),
  (.branch 41 (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (-43)) (.leaf (-42))) (.branch 23 (.leaf (-41)) (.branch 24 (.leaf (-40)) (.leaf (-39))))) (.branch 27 (.branch 26 (.leaf (-38)) (.leaf (-37))) (.branch 28 (.leaf (-36)) (.branch 29 (.leaf (-35)) (.leaf (-34)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (-33)) (.leaf (-32))) (.branch 33 (.leaf (-31)) (.branch 34 (.leaf (-30)) (.leaf (-29))))) (.branch 38 (.branch 36 (.leaf (-28)) (.branch 37 (.leaf (-27)) (.leaf (-26)))) (.branch 39 (.leaf (-25)) (.branch 40 (.leaf (-24)) (.leaf (-23))))))) (.branch 52 (.branch 46 (.branch 43 (.branch 42 (.leaf (-22)) (.leaf (-21))) (.branch 44 (.leaf (-20)) (.branch 45 (.leaf (-19)) (.leaf (-18))))) (.branch 49 (.branch 47 (.leaf (-17)) (.branch 48 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.leaf (-14)) (.branch 51 (.leaf (-13)) (.leaf (-12)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7))))) (.branch 60 (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 61 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 46 (.branch 43 (.branch 42 (.leaf (-22)) (.leaf (-21))) (.branch 44 (.leaf (-20)) (.branch 45 (.leaf (-19)) (.leaf (-18))))) (.branch 49 (.branch 47 (.leaf (-17)) (.branch 48 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.leaf (-14)) (.branch 51 (.leaf (-13)) (.leaf (-12)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7))))) (.branch 60 (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 61 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_150_1319 : CycleWitness 8 where
  length := 63
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (0))))))) (.branch 47 (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (6))) (.branch 38 (.leaf (0)) (.leaf (1))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (1)))))) (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (0)) (.leaf (4))) (.branch 50 (.leaf (0)) (.leaf (1)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (3))) (.branch 54 (.leaf (2)) (.leaf (0))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (1)) (.leaf (0))) (.branch 58 (.leaf (7)) (.leaf (0)))) (.branch 61 (.branch 60 (.leaf (1)) (.leaf (2))) (.branch 62 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1319
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))) (.branch 27 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.leaf (13)))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16)))) (.branch 43 (.branch 41 (.leaf (17)) (.leaf (18))) (.branch 45 (.leaf (19)) (.leaf (20))))) (.branch 55 (.branch 50 (.leaf (21)) (.branch 52 (.leaf (22)) (.leaf (23)))) (.branch 59 (.branch 57 (.leaf (24)) (.leaf (25))) (.branch 62 (.leaf (26)) (.leaf (27))))))),
  (.branch 30 (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1))),
  (.branch 58 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 26 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 9 (.leaf (-11)) (.leaf (-12)))) (.branch 47 (.branch 30 (.leaf (-13)) (.leaf (-14))) (.branch 51 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-47))),
  (.branch 37 (.leaf (0)) (.leaf (-26))),
  (.branch 58 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 60 (.leaf (-5)) (.leaf (-3))),
  (.branch 61 (.branch 52 (.leaf (-16)) (.leaf (-15))) (.branch 62 (.leaf (-12)) (.leaf (-9)))),
  (.branch 47 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 56 (.branch 52 (.branch 50 (.leaf (-14)) (.branch 51 (.leaf (-13)) (.leaf (-12)))) (.branch 54 (.branch 53 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.leaf (-8))))) (.branch 59 (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 61 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 62 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-47)) (.leaf (-46))) (.branch 19 (.leaf (-45)) (.branch 20 (.leaf (-44)) (.leaf (-43))))) (.branch 24 (.branch 22 (.leaf (-42)) (.branch 23 (.leaf (-41)) (.leaf (-40)))) (.branch 25 (.leaf (-39)) (.branch 26 (.leaf (-38)) (.leaf (-37)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-36)) (.branch 29 (.leaf (-35)) (.leaf (-34)))) (.branch 31 (.leaf (-33)) (.branch 32 (.leaf (-32)) (.leaf (-31))))) (.branch 36 (.branch 34 (.leaf (-30)) (.branch 35 (.leaf (-29)) (.leaf (-28)))) (.branch 37 (.leaf (-27)) (.branch 38 (.leaf (-26)) (.leaf (-25))))))) (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-24)) (.branch 41 (.leaf (-23)) (.leaf (-22)))) (.branch 43 (.leaf (-21)) (.branch 44 (.leaf (-20)) (.leaf (-19))))) (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7))))) (.branch 60 (.branch 58 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 61 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 50 (.branch 43 (.branch 40 (.branch 38 (.leaf (-26)) (.branch 39 (.leaf (-25)) (.leaf (-24)))) (.branch 41 (.leaf (-23)) (.branch 42 (.leaf (-22)) (.leaf (-21))))) (.branch 46 (.branch 44 (.leaf (-20)) (.branch 45 (.leaf (-19)) (.leaf (-18)))) (.branch 48 (.branch 47 (.leaf (-17)) (.leaf (-16))) (.branch 49 (.leaf (-15)) (.leaf (-14)))))) (.branch 56 (.branch 53 (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11)))) (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-8))))) (.branch 59 (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 61 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 62 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 60 (.branch 59 (.leaf (-5)) (.leaf (-4))) (.branch 61 (.leaf (-3)) (.branch 62 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_150_1320 : CycleWitness 8 where
  length := 63
  word := (.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (5))) (.branch 14 (.leaf (0)) (.leaf (1)))))) (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (3)) (.leaf (2))) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 21 (.branch 20 (.leaf (2)) (.leaf (4))) (.branch 22 (.leaf (0)) (.leaf (1))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (3)) (.leaf (0)))) (.branch 29 (.branch 28 (.leaf (1)) (.leaf (2))) (.branch 30 (.leaf (4)) (.leaf (0))))))) (.branch 47 (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (1)) (.leaf (2))) (.branch 42 (.leaf (4)) (.leaf (0)))) (.branch 45 (.branch 44 (.leaf (1)) (.leaf (0))) (.branch 46 (.leaf (2)) (.leaf (3)))))) (.branch 55 (.branch 51 (.branch 49 (.branch 48 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (4)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (7))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (3)) (.leaf (2)))) (.branch 61 (.branch 60 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_1320
  counts := ![(.branch 27 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 45 (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.branch 43 (.leaf (12)) (.leaf (13))))) (.branch 52 (.branch 48 (.leaf (14)) (.leaf (15))) (.branch 56 (.leaf (16)) (.branch 60 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 49 (.branch 40 (.branch 36 (.leaf (8)) (.leaf (9))) (.branch 44 (.leaf (10)) (.leaf (11)))) (.branch 57 (.branch 53 (.leaf (12)) (.leaf (13))) (.branch 61 (.leaf (14)) (.leaf (15)))))),
  (.branch 33 (.branch 17 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 41 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 54 (.leaf (12)) (.leaf (13))) (.branch 62 (.leaf (14)) (.leaf (15)))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 24 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 6 (.leaf (-18)) (.leaf (-21)))) (.branch 45 (.branch 27 (.leaf (-24)) (.leaf (-27))) (.branch 48 (.leaf (-30)) (.leaf (-33))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))) (.branch 41 (.branch 20 (.leaf (-3)) (.leaf (-5))) (.branch 62 (.leaf (-6)) (.leaf (-7))))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 30 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 51 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.leaf (-50))),
  (.branch 34 (.leaf (0)) (.leaf (-29))),
  (.branch 55 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 57 (.branch 49 (.leaf (-33)) (.branch 53 (.leaf (-32)) (.leaf (-31)))) (.branch 61 (.leaf (-30)) (.branch 62 (.leaf (-26)) (.leaf (-22))))),
  (.branch 45 (.leaf (-11)) (.branch 62 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-7)),
  (.branch 60 (.branch 48 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-8)))) (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-4)) (.leaf (-2))))),
  (.branch 53 (.branch 52 (.leaf (-4)) (.leaf (-3))) (.branch 54 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 38 (.branch 25 (.branch 19 (.branch 16 (.branch 14 (.leaf (-50)) (.branch 15 (.leaf (-49)) (.leaf (-48)))) (.branch 17 (.leaf (-47)) (.branch 18 (.leaf (-46)) (.leaf (-45))))) (.branch 22 (.branch 20 (.leaf (-44)) (.branch 21 (.leaf (-43)) (.leaf (-42)))) (.branch 23 (.leaf (-41)) (.branch 24 (.leaf (-40)) (.leaf (-39)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-38)) (.branch 27 (.leaf (-37)) (.leaf (-36)))) (.branch 29 (.leaf (-35)) (.branch 30 (.leaf (-34)) (.leaf (-33))))) (.branch 34 (.branch 32 (.leaf (-32)) (.branch 33 (.leaf (-31)) (.leaf (-30)))) (.branch 36 (.branch 35 (.leaf (-29)) (.leaf (-28))) (.branch 37 (.leaf (-27)) (.leaf (-26))))))) (.branch 50 (.branch 44 (.branch 41 (.branch 39 (.leaf (-25)) (.branch 40 (.leaf (-24)) (.leaf (-23)))) (.branch 42 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20))))) (.branch 47 (.branch 45 (.leaf (-19)) (.branch 46 (.leaf (-18)) (.leaf (-17)))) (.branch 48 (.leaf (-16)) (.branch 49 (.leaf (-15)) (.leaf (-14)))))) (.branch 56 (.branch 53 (.branch 51 (.leaf (-13)) (.branch 52 (.leaf (-12)) (.leaf (-11)))) (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-9)) (.leaf (-8))))) (.branch 59 (.branch 57 (.leaf (-7)) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 61 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 62 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 41 (.branch 37 (.branch 35 (.leaf (-29)) (.branch 36 (.leaf (-28)) (.leaf (-27)))) (.branch 39 (.branch 38 (.leaf (-26)) (.leaf (-25))) (.branch 40 (.leaf (-24)) (.leaf (-23))))) (.branch 44 (.branch 42 (.leaf (-22)) (.branch 43 (.leaf (-21)) (.leaf (-20)))) (.branch 46 (.branch 45 (.leaf (-19)) (.leaf (-18))) (.branch 47 (.leaf (-17)) (.leaf (-16)))))) (.branch 55 (.branch 51 (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13)))) (.branch 53 (.branch 52 (.leaf (-12)) (.leaf (-11))) (.branch 54 (.leaf (-10)) (.leaf (-9))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 61 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 62 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-8)) (.leaf (-7))) (.branch 58 (.leaf (-6)) (.leaf (-5)))) (.branch 61 (.branch 60 (.leaf (-4)) (.leaf (-3))) (.branch 62 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_150 : Fin 15 → CycleWitness 8 := ![witnessD8_150_1306, witnessD8_150_1307, witnessD8_150_1308, witnessD8_150_1309, witnessD8_150_1310, witnessD8_150_1311, witnessD8_150_1312, witnessD8_150_1313, witnessD8_150_1314, witnessD8_150_1315, witnessD8_150_1316, witnessD8_150_1317, witnessD8_150_1318, witnessD8_150_1319, witnessD8_150_1320]
end RealPinwheel.FiveSixths


