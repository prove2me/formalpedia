-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_146
-- name    : RealPinwheel_FiveSixths_WitnessD8_146
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:07:55.076213+00:00
-- url     : https://prove2.me/theorems/d4fbb130-0c62-4faa-8e66-05f09bfe2d89
-- title:
--   Exact witness block D8_146
-- statement:
--   These exact witnesses represent words 1247 through 1261 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1247–1261; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_146_1246 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (5)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (7)) (.leaf (2)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1246
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))) (.branch 26 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.leaf (13)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16)))) (.branch 42 (.branch 40 (.leaf (17)) (.leaf (18))) (.branch 45 (.leaf (19)) (.leaf (20))))) (.branch 56 (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24)))) (.branch 61 (.branch 58 (.leaf (25)) (.leaf (26))) (.branch 63 (.leaf (27)) (.leaf (28))))))),
  (.branch 30 (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 41 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 57 (.leaf (14)) (.branch 62 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 59 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-37))),
  (.branch 59 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 52 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 58 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 36 (.branch 31 (.branch 29 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.branch 35 (.leaf (-30)) (.leaf (-29)))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.leaf (-25)))) (.branch 42 (.branch 41 (.leaf (-24)) (.leaf (-23))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))))) (.branch 54 (.branch 49 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))) (.branch 51 (.branch 50 (.leaf (-15)) (.leaf (-14))) (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))))) (.branch 59 (.branch 56 (.branch 55 (.leaf (-10)) (.leaf (-9))) (.branch 57 (.leaf (-8)) (.branch 58 (.leaf (-7)) (.leaf (-6))))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_146_1247 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (4)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (7)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1247
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 56 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 53 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 58 (.leaf (14)) (.branch 61 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-37))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 60 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 57 (.branch 54 (.branch 10 (.leaf (-37)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 42 (.leaf (-5)) (.leaf (-3)))]
def witnessD8_146_1248 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (5)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1248
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 31 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 56 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 63 (.leaf (19)) (.leaf (20))))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-41))),
  (.branch 55 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 57 (.leaf (-8)) (.leaf (-5))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 33 (.branch 28 (.branch 25 (.branch 24 (.leaf (-41)) (.leaf (-40))) (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37))))) (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27))))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))))) (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_146_1249 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (7))) (.branch 31 (.leaf (0)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (5)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (6))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (7))) (.branch 63 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_1249
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))) (.branch 26 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 28 (.leaf (12)) (.leaf (13)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16)))) (.branch 42 (.branch 40 (.leaf (17)) (.leaf (18))) (.branch 44 (.leaf (19)) (.leaf (20))))) (.branch 56 (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24)))) (.branch 60 (.branch 58 (.leaf (25)) (.leaf (26))) (.branch 63 (.leaf (27)) (.leaf (28))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2)))),
  (.branch 30 (.leaf (0)) (.branch 62 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 21 (.leaf (0)) (.branch 41 (.leaf (-1)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 61 (.leaf (-12)) (.leaf (-7))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 43 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 55 (.branch 50 (.branch 48 (.branch 47 (.leaf (-18)) (.leaf (-17))) (.branch 49 (.leaf (-16)) (.leaf (-15)))) (.branch 52 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_146_1250 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (5)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (3)) (.leaf (0))) (.branch 39 (.leaf (6)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (2))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (3)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (1))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (0))) (.branch 63 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_1250
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 56 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 32 (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))) (.branch 48 (.branch 37 (.leaf (-4)) (.leaf (-5))) (.branch 53 (.leaf (-6)) (.leaf (-7))))),
  (.branch 7 (.leaf (0)) (.leaf (-57))),
  (.branch 23 (.leaf (0)) (.leaf (-41))),
  (.branch 39 (.leaf (0)) (.leaf (-25))),
  (.branch 55 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 62 (.branch 51 (.leaf (-10)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.leaf (-4)) (.leaf (-3))),
  (.branch 61 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 35 (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-57)) (.branch 9 (.leaf (-56)) (.leaf (-55)))) (.branch 12 (.branch 11 (.leaf (-54)) (.leaf (-53))) (.branch 13 (.leaf (-52)) (.leaf (-51))))) (.branch 17 (.branch 15 (.leaf (-50)) (.branch 16 (.leaf (-49)) (.leaf (-48)))) (.branch 19 (.branch 18 (.leaf (-47)) (.leaf (-46))) (.branch 20 (.leaf (-45)) (.leaf (-44)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-43)) (.branch 23 (.leaf (-42)) (.leaf (-41)))) (.branch 26 (.branch 25 (.leaf (-40)) (.leaf (-39))) (.branch 27 (.leaf (-38)) (.leaf (-37))))) (.branch 31 (.branch 29 (.leaf (-36)) (.branch 30 (.leaf (-35)) (.leaf (-34)))) (.branch 33 (.branch 32 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-31)) (.leaf (-30))))))) (.branch 49 (.branch 42 (.branch 38 (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27)))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.leaf (-23))))) (.branch 45 (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20)))) (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.leaf (-16)))))) (.branch 56 (.branch 52 (.branch 50 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 33 (.branch 28 (.branch 25 (.branch 24 (.leaf (-41)) (.leaf (-40))) (.branch 26 (.leaf (-39)) (.branch 27 (.leaf (-38)) (.leaf (-37))))) (.branch 30 (.branch 29 (.leaf (-36)) (.leaf (-35))) (.branch 31 (.leaf (-34)) (.branch 32 (.leaf (-33)) (.leaf (-32)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-31)) (.leaf (-30))) (.branch 36 (.leaf (-29)) (.branch 37 (.leaf (-28)) (.leaf (-27))))) (.branch 40 (.branch 39 (.leaf (-26)) (.leaf (-25))) (.branch 41 (.leaf (-24)) (.branch 42 (.leaf (-23)) (.leaf (-22))))))) (.branch 53 (.branch 48 (.branch 45 (.branch 44 (.leaf (-21)) (.leaf (-20))) (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17))))) (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))))) (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_146_1251 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (6)) (.leaf (0))) (.branch 43 (.leaf (2)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (3))) (.branch 47 (.leaf (0)) (.leaf (4)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (7)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (5)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (3))) (.branch 63 (.leaf (0)) (.leaf (6))))))))
  code := certificateD8_1251
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))) (.branch 26 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 28 (.leaf (12)) (.leaf (13)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16)))) (.branch 42 (.branch 40 (.leaf (17)) (.leaf (18))) (.branch 44 (.leaf (19)) (.leaf (20))))) (.branch 56 (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24)))) (.branch 60 (.branch 58 (.leaf (25)) (.leaf (26))) (.branch 63 (.leaf (27)) (.leaf (28))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-17)) (.leaf (-19)))),
  (.branch 37 (.branch 16 (.leaf (0)) (.leaf (-6))) (.branch 57 (.leaf (-7)) (.leaf (-9)))),
  (.branch 21 (.leaf (0)) (.branch 41 (.leaf (-1)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 61 (.leaf (-12)) (.leaf (-7))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 55 (.branch 51 (.branch 49 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.leaf (-12))))) (.branch 59 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8)))) (.branch 61 (.branch 60 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))))),
  (.branch 60 (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7)))) (.branch 62 (.branch 61 (.leaf (-6)) (.leaf (-5))) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 43 (.branch 42 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 61 (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))))]
def witnessD8_146_1252 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (7)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (6)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (7)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (3))) (.branch 43 (.leaf (0)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (5))) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_1252
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))) (.branch 48 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (-2))) (.branch 48 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 56 (.leaf (-39)) (.leaf (-40)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-4)) (.leaf (-8)))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 60 (.branch 49 (.leaf (-6)) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.branch 61 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-40)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 38 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 59 (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-8))) (.branch 58 (.leaf (-7)) (.leaf (-6)))) (.branch 61 (.branch 60 (.leaf (-5)) (.leaf (-4))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.branch 45 (.branch 42 (.branch 40 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 43 (.leaf (-22)) (.branch 44 (.leaf (-21)) (.leaf (-20))))) (.branch 48 (.branch 46 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-17)))) (.branch 49 (.leaf (-16)) (.branch 50 (.leaf (-15)) (.leaf (-14)))))) (.branch 57 (.branch 54 (.branch 52 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-11)))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-9)) (.leaf (-8))))) (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_146_1253 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (0)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))) (.branch 38 (.branch 37 (.leaf (5)) (.leaf (0))) (.branch 39 (.leaf (3)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (7)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (4)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (3)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (2)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (7))) (.branch 63 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1253
  counts := ![(.branch 31 (.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 22 (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))) (.branch 26 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.leaf (13)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16)))) (.branch 42 (.branch 40 (.leaf (17)) (.leaf (18))) (.branch 45 (.leaf (19)) (.leaf (20))))) (.branch 56 (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24)))) (.branch 61 (.branch 58 (.leaf (25)) (.leaf (26))) (.branch 63 (.leaf (27)) (.leaf (28))))))),
  (.branch 27 (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 59 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-4))) (.branch 48 (.leaf (-6)) (.leaf (-7)))),
  (.branch 32 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-37)) (.leaf (-38)))),
  (.branch 41 (.branch 20 (.leaf (0)) (.leaf (-4))) (.branch 62 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 52 (.leaf (-11)) (.branch 59 (.leaf (-10)) (.leaf (-7)))),
  (.branch 61 (.branch 51 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 58 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 61 (.branch 49 (.leaf (-7)) (.leaf (-6))) (.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3))))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 57 (.branch 54 (.branch 31 (.leaf (-38)) (.branch 53 (.leaf (-36)) (.leaf (-33)))) (.branch 55 (.leaf (-30)) (.branch 56 (.leaf (-27)) (.leaf (-24))))) (.branch 60 (.branch 58 (.leaf (-21)) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 63 (.leaf (-6)) (.leaf (-3)))]
def witnessD8_146_1254 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (5))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (1))) (.branch 39 (.leaf (0)) (.leaf (4))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (2)) (.leaf (0))) (.branch 43 (.leaf (1)) (.leaf (7)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (3))) (.branch 47 (.leaf (1)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (3))) (.branch 55 (.leaf (0)) (.leaf (4))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (1)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (7)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_1254
  counts := ![(.branch 29 (.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))) (.branch 45 (.branch 35 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 39 (.leaf (12)) (.branch 42 (.leaf (13)) (.leaf (14))))) (.branch 55 (.branch 49 (.leaf (15)) (.branch 51 (.leaf (16)) (.leaf (17)))) (.branch 58 (.leaf (18)) (.branch 61 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 47 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 41 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 36 (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 46 (.leaf (4)) (.leaf (5))) (.branch 63 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 60 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 19 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-14)))) (.branch 35 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))) (.branch 38 (.leaf (-11)) (.branch 47 (.leaf (-12)) (.leaf (-13))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-26))) (.branch 31 (.leaf (-28)) (.leaf (-29)))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))) (.branch 54 (.branch 36 (.leaf (-3)) (.leaf (-4))) (.branch 63 (.leaf (-6)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 62 (.branch 52 (.leaf (-17)) (.leaf (-16))) (.branch 63 (.leaf (-12)) (.leaf (-8)))),
  (.branch 53 (.branch 48 (.leaf (-13)) (.leaf (-12))) (.branch 58 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-7))))),
  (.branch 61 (.branch 32 (.leaf (-29)) (.branch 60 (.leaf (-27)) (.leaf (-22)))) (.branch 62 (.leaf (-17)) (.branch 63 (.leaf (-12)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_146_1255 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (7))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (0)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 47 (.leaf (0)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (0)) (.leaf (5)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1255
  counts := ![(.branch 31 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.leaf (15)))))) (.branch 47 (.branch 39 (.branch 35 (.branch 33 (.leaf (16)) (.leaf (17))) (.branch 37 (.leaf (18)) (.leaf (19)))) (.branch 43 (.branch 41 (.leaf (20)) (.leaf (21))) (.branch 45 (.leaf (22)) (.leaf (23))))) (.branch 55 (.branch 51 (.branch 49 (.leaf (24)) (.leaf (25))) (.branch 53 (.leaf (26)) (.leaf (27)))) (.branch 59 (.branch 57 (.leaf (28)) (.leaf (29))) (.branch 61 (.leaf (30)) (.branch 63 (.leaf (31)) (.leaf (32)))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 58 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 46 (.branch 38 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 32 (.leaf (0)) (.branch 64 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-15))) (.branch 44 (.leaf (-22)) (.leaf (-27)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (-15)) (.leaf (-18)))),
  (.branch 40 (.branch 20 (.leaf (0)) (.leaf (-3))) (.branch 60 (.leaf (-6)) (.leaf (-9)))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 59 (.branch 57 (.branch 45 (.leaf (-27)) (.leaf (-26))) (.branch 58 (.leaf (-24)) (.leaf (-22)))) (.branch 61 (.branch 60 (.leaf (-20)) (.leaf (-18))) (.branch 62 (.leaf (-16)) (.branch 63 (.leaf (-14)) (.leaf (-12)))))),
  (.branch 57 (.branch 54 (.branch 29 (.leaf (-18)) (.branch 53 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-14)) (.leaf (-13))))) (.branch 60 (.branch 58 (.leaf (-12)) (.branch 59 (.leaf (-11)) (.leaf (-10)))) (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 62 (.branch 61 (.leaf (-9)) (.leaf (-8))) (.branch 63 (.leaf (-7)) (.leaf (-6)))),
  (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (-16)) (.leaf (-15))) (.branch 51 (.leaf (-14)) (.leaf (-13)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_146_1256 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (7))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (5))) (.branch 31 (.leaf (0)) (.leaf (6))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (2))) (.branch 39 (.leaf (1)) (.leaf (0))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (4)) (.leaf (0))) (.branch 43 (.leaf (7)) (.leaf (0)))) (.branch 46 (.branch 45 (.leaf (1)) (.leaf (5))) (.branch 47 (.leaf (0)) (.leaf (2)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (6))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (4)) (.leaf (0))) (.branch 59 (.leaf (2)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (1)) (.leaf (5))) (.branch 63 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1256
  counts := ![(.branch 31 (.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 21 (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))) (.branch 26 (.branch 24 (.leaf (10)) (.leaf (11))) (.branch 28 (.leaf (12)) (.leaf (13)))))) (.branch 47 (.branch 37 (.branch 33 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16)))) (.branch 42 (.branch 40 (.leaf (17)) (.leaf (18))) (.branch 44 (.leaf (19)) (.leaf (20))))) (.branch 56 (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 53 (.leaf (23)) (.leaf (24)))) (.branch 60 (.branch 58 (.leaf (25)) (.leaf (26))) (.branch 63 (.leaf (27)) (.leaf (28))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 45 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 50 (.leaf (9)) (.leaf (10))) (.branch 61 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 48 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 59 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 43 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 64 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (-31)) (.leaf (-32)))),
  (.leaf (0))]
  high := ![(.branch 54 (.leaf (-13)) (.branch 61 (.leaf (-12)) (.leaf (-7)))),
  (.branch 62 (.branch 56 (.leaf (-11)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 49 (.leaf (-16)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 60 (.branch 58 (.leaf (-7)) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 63 (.leaf (-2)) (.leaf (-1))),
  (.branch 58 (.branch 55 (.branch 33 (.leaf (-32)) (.leaf (-30))) (.branch 56 (.leaf (-27)) (.branch 57 (.leaf (-24)) (.leaf (-21))))) (.branch 61 (.branch 59 (.leaf (-18)) (.branch 60 (.leaf (-15)) (.leaf (-12)))) (.branch 62 (.leaf (-9)) (.branch 63 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD8_146_1257 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (7))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (5)) (.leaf (2))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (4)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (7))) (.branch 43 (.leaf (0)) (.leaf (1)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (3))) (.branch 47 (.leaf (0)) (.leaf (5)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (6))) (.branch 55 (.leaf (1)) (.leaf (0))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (3)) (.leaf (2))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (7))) (.branch 63 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_1257
  counts := ![(.branch 29 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))) (.branch 47 (.branch 38 (.branch 33 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13)))) (.branch 41 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))) (.branch 56 (.branch 50 (.leaf (17)) (.branch 52 (.leaf (18)) (.leaf (19)))) (.branch 59 (.leaf (20)) (.branch 61 (.leaf (21)) (.leaf (22))))))),
  (.branch 28 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 55 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 60 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 39 (.leaf (5)) (.branch 45 (.leaf (6)) (.leaf (7)))) (.branch 58 (.leaf (8)) (.branch 64 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3)))),
  (.branch 42 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 11 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-9)))) (.branch 44 (.leaf (-10)) (.branch 49 (.leaf (-11)) (.leaf (-12))))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (-13)) (.leaf (-16)))),
  (.branch 42 (.branch 22 (.leaf (0)) (.leaf (-1))) (.branch 62 (.leaf (-4)) (.leaf (-7))))]
  high := ![(.branch 62 (.leaf (-5)) (.branch 63 (.leaf (-4)) (.leaf (-3)))),
  (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-10))) (.branch 63 (.leaf (-8)) (.leaf (-6)))),
  (.branch 52 (.leaf (-1)) (.leaf (0))),
  (.branch 60 (.branch 58 (.branch 47 (.leaf (-22)) (.leaf (-21))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 58 (.branch 55 (.branch 31 (.leaf (-16)) (.leaf (-15))) (.branch 56 (.leaf (-14)) (.branch 57 (.leaf (-13)) (.leaf (-12))))) (.branch 61 (.branch 59 (.leaf (-11)) (.branch 60 (.leaf (-10)) (.leaf (-9)))) (.branch 62 (.leaf (-8)) (.branch 63 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 63 (.leaf (-7)) (.leaf (-6)))]
def witnessD8_146_1258 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (7))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (4))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (6)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (7))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 43 (.leaf (4)) (.leaf (5)))) (.branch 46 (.branch 45 (.leaf (3)) (.leaf (0))) (.branch 47 (.leaf (2)) (.leaf (1)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (7)) (.leaf (0))) (.branch 59 (.leaf (1)) (.leaf (3)))) (.branch 62 (.branch 61 (.leaf (0)) (.leaf (2))) (.branch 63 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_1258
  counts := ![(.branch 30 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))) (.branch 54 (.branch 50 (.leaf (13)) (.leaf (14))) (.branch 58 (.leaf (15)) (.branch 61 (.leaf (16)) (.leaf (17))))))),
  (.branch 29 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 59 (.leaf (9)) (.leaf (10)))))),
  (.branch 33 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 53 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 64 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 63 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-26))) (.branch 22 (.leaf (-43)) (.leaf (-47)))),
  (.branch 35 (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-24)) (.leaf (-25)))) (.branch 41 (.leaf (-29)) (.branch 52 (.leaf (-33)) (.leaf (-46))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 39 (.leaf (-29)) (.leaf (-33)))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-30)))) (.branch 36 (.branch 28 (.leaf (-31)) (.leaf (-32))) (.branch 51 (.leaf (-33)) (.leaf (-42))))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 56 (.leaf (-39)) (.leaf (-40)))),
  (.branch 37 (.branch 13 (.leaf (0)) (.leaf (-2))) (.branch 49 (.leaf (-12)) (.leaf (-17)))),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 62 (.branch 23 (.leaf (-47)) (.leaf (-46))) (.branch 63 (.leaf (-37)) (.leaf (-28)))),
  (.branch 61 (.branch 53 (.leaf (-46)) (.branch 60 (.leaf (-45)) (.leaf (-40)))) (.branch 62 (.leaf (-35)) (.branch 63 (.leaf (-30)) (.leaf (-25))))),
  (.branch 40 (.leaf (-33)) (.branch 63 (.leaf (-32)) (.leaf (-27)))),
  (.branch 61 (.branch 52 (.leaf (-42)) (.leaf (-36))) (.branch 62 (.leaf (-29)) (.branch 63 (.leaf (-22)) (.leaf (-15))))),
  (.branch 11 (.leaf (-2)) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-40)) (.leaf (-35))) (.branch 59 (.leaf (-30)) (.leaf (-25)))) (.branch 62 (.branch 61 (.leaf (-20)) (.leaf (-15))) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 50 (.leaf (-17)) (.leaf (-16))),
  (.branch 60 (.branch 58 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_146_1259 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (6)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (6)) (.leaf (3))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (4)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (2)) (.leaf (1))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (5))) (.branch 43 (.leaf (0)) (.leaf (3)))) (.branch 46 (.branch 45 (.leaf (2)) (.leaf (0))) (.branch 47 (.leaf (1)) (.leaf (6)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (3))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (5))) (.branch 59 (.leaf (0)) (.leaf (1)))) (.branch 62 (.branch 61 (.leaf (2)) (.leaf (0))) (.branch 63 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_1259
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))) (.branch 46 (.branch 38 (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17))))) (.branch 54 (.branch 49 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 59 (.branch 57 (.leaf (21)) (.leaf (22))) (.branch 62 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 53 (.leaf (8)) (.branch 60 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 36 (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 50 (.leaf (3)) (.branch 64 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.branch 63 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-22)) (.leaf (-24)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-5)))) (.branch 45 (.leaf (-7)) (.branch 61 (.leaf (-9)) (.leaf (-11))))),
  (.branch 44 (.branch 4 (.leaf (0)) (.leaf (-19))) (.branch 56 (.leaf (-20)) (.leaf (-23)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 36 (.leaf (-6)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 60 (.leaf (-7)) (.branch 63 (.leaf (-6)) (.leaf (-3)))),
  (.branch 61 (.branch 41 (.leaf (-24)) (.branch 54 (.leaf (-23)) (.leaf (-20)))) (.branch 62 (.leaf (-15)) (.branch 63 (.leaf (-10)) (.leaf (-5))))),
  (.branch 62 (.leaf (-11)) (.branch 63 (.leaf (-10)) (.leaf (-9)))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-23)) (.leaf (-21))) (.branch 59 (.leaf (-19)) (.leaf (-17)))) (.branch 62 (.branch 61 (.leaf (-15)) (.leaf (-13))) (.branch 63 (.leaf (-11)) (.leaf (-9))))),
  (.branch 52 (.branch 37 (.leaf (-9)) (.branch 51 (.leaf (-8)) (.leaf (-6)))) (.branch 53 (.leaf (-4)) (.branch 54 (.leaf (-2)) (.leaf (0))))),
  (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 58 (.branch 55 (.branch 53 (.leaf (-12)) (.branch 54 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_146_1260 : CycleWitness 8 where
  length := 64
  word := (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (1))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (0)) (.leaf (3)))) (.branch 38 (.branch 37 (.leaf (7)) (.leaf (0))) (.branch 39 (.leaf (1)) (.leaf (5))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (0)) (.leaf (4))) (.branch 43 (.leaf (0)) (.leaf (2)))) (.branch 46 (.branch 45 (.leaf (6)) (.leaf (0))) (.branch 47 (.leaf (3)) (.leaf (0)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (7)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (5))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (0)) (.leaf (3))) (.branch 59 (.leaf (1)) (.leaf (0)))) (.branch 62 (.branch 61 (.leaf (6)) (.leaf (0))) (.branch 63 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_1260
  counts := ![(.branch 30 (.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))) (.branch 48 (.branch 38 (.branch 33 (.leaf (13)) (.branch 35 (.leaf (14)) (.leaf (15)))) (.branch 43 (.branch 41 (.leaf (16)) (.leaf (17))) (.branch 46 (.leaf (18)) (.leaf (19))))) (.branch 55 (.branch 50 (.leaf (20)) (.branch 52 (.leaf (21)) (.leaf (22)))) (.branch 60 (.branch 57 (.leaf (23)) (.leaf (24))) (.branch 62 (.leaf (25)) (.leaf (26))))))),
  (.branch 32 (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 59 (.leaf (6)) (.leaf (7))))),
  (.branch 34 (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))) (.branch 54 (.branch 44 (.leaf (4)) (.leaf (5))) (.branch 64 (.leaf (6)) (.leaf (7))))),
  (.branch 26 (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 42 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.branch 52 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 39 (.leaf (-23)) (.leaf (-28)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-8)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 63 (.leaf (-6)) (.leaf (-4))),
  (.branch 60 (.branch 40 (.leaf (-28)) (.branch 50 (.leaf (-27)) (.leaf (-26)))) (.branch 62 (.branch 61 (.leaf (-23)) (.leaf (-20))) (.branch 63 (.leaf (-17)) (.leaf (-14))))),
  (.branch 55 (.branch 35 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-9)) (.leaf (-6))) (.branch 58 (.leaf (-3)) (.leaf (0))))),
  (.branch 60 (.branch 48 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 59 (.leaf (-18)) (.leaf (-15)))) (.branch 62 (.branch 61 (.leaf (-12)) (.leaf (-9))) (.branch 63 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.leaf (-4)) (.leaf (-3))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-8)) (.leaf (-7))) (.branch 59 (.leaf (-6)) (.leaf (-5)))) (.branch 62 (.branch 61 (.leaf (-4)) (.leaf (-3))) (.branch 63 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1)))),
  (.branch 58 (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-10))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7))))) (.branch 61 (.branch 59 (.leaf (-6)) (.branch 60 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.leaf (-3)) (.branch 63 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_146 : Fin 15 → CycleWitness 8 := ![witnessD8_146_1246, witnessD8_146_1247, witnessD8_146_1248, witnessD8_146_1249, witnessD8_146_1250, witnessD8_146_1251, witnessD8_146_1252, witnessD8_146_1253, witnessD8_146_1254, witnessD8_146_1255, witnessD8_146_1256, witnessD8_146_1257, witnessD8_146_1258, witnessD8_146_1259, witnessD8_146_1260]
end RealPinwheel.FiveSixths


