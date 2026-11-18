-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_026
-- name    : RealPinwheel_FiveSixths_WitnessD7_026
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:38:45.172599+00:00
-- url     : https://prove2.me/theorems/24737ffb-fe78-464c-b24a-9fc574881820
-- title:
--   Exact witness block D7_026
-- statement:
--   These exact witnesses represent words 290 through 306 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 290–306; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_026_289 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (4))) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (4)) (.leaf (2)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (1)) (.leaf (0))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (0)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_289
  counts := ![(.branch 27 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 44 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 39 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-3)))) (.branch 42 (.leaf (-4)) (.branch 57 (.leaf (-6)) (.leaf (-7))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 52 (.leaf (-17)) (.leaf (-22)))),
  (.branch 29 (.branch 10 (.leaf (0)) (.leaf (-28))) (.branch 48 (.leaf (-29)) (.leaf (-30)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 36 (.branch 33 (.leaf (-28)) (.leaf (-27))) (.branch 39 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 51 (.branch 48 (.leaf (-23)) (.leaf (-22))) (.branch 54 (.leaf (-21)) (.branch 57 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 44 (.branch 32 (.leaf (-19)) (.branch 38 (.leaf (-18)) (.leaf (-17)))) (.branch 56 (.branch 50 (.leaf (-16)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 55 (.branch 47 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-10)) (.branch 57 (.leaf (-8)) (.leaf (-6))))),
  (.leaf (-7)),
  (.branch 55 (.branch 53 (.leaf (-22)) (.branch 54 (.leaf (-20)) (.leaf (-18)))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-30)) (.leaf (-27))) (.branch 51 (.leaf (-24)) (.branch 52 (.leaf (-21)) (.leaf (-18))))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0)))]
def witnessD7_026_290 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (6)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (5))) (.branch 28 (.leaf (1)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (4))) (.branch 35 (.leaf (3)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (3))) (.branch 42 (.leaf (2)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (5)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (4)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (0)) (.leaf (3))) (.branch 53 (.leaf (2)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (0)) (.leaf (6))) (.branch 57 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_290
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 32 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 50 (.leaf (9)) (.branch 54 (.leaf (10)) (.leaf (11)))))),
  (.branch 31 (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 53 (.leaf (9)) (.branch 57 (.leaf (10)) (.leaf (11)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 46 (.branch 35 (.leaf (5)) (.branch 41 (.leaf (6)) (.leaf (7)))) (.branch 52 (.leaf (8)) (.branch 58 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-5)))) (.branch 32 (.leaf (-6)) (.branch 43 (.leaf (-8)) (.leaf (-9))))),
  (.branch 28 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))) (.branch 33 (.leaf (-22)) (.branch 54 (.leaf (-24)) (.leaf (-27))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 57 (.leaf (-10)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-12))) (.branch 45 (.leaf (-15)) (.leaf (-18)))),
  (.branch 16 (.leaf (0)) (.branch 56 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-7)))),
  (.branch 56 (.branch 55 (.leaf (-27)) (.leaf (-22))) (.branch 57 (.leaf (-17)) (.leaf (-12)))),
  (.leaf (-12)),
  (.branch 47 (.leaf (-2)) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 53 (.branch 50 (.branch 35 (.leaf (-19)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 49 (.leaf (-15)) (.branch 50 (.leaf (-14)) (.leaf (-13))))) (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6)))))),
  (.branch 57 (.leaf (-7)) (.leaf (-6)))]
def witnessD7_026_291 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (6)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (6)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (3))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (5))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (3))) (.branch 42 (.leaf (6)) (.leaf (0)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (1)) (.leaf (4)))) (.branch 48 (.branch 47 (.leaf (0)) (.leaf (5))) (.branch 49 (.leaf (0)) (.leaf (2))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (3))) (.branch 53 (.leaf (0)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (6)) (.leaf (2))) (.branch 57 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_291
  counts := ![(.branch 28 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 43 (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 49 (.branch 47 (.leaf (14)) (.leaf (15))) (.branch 53 (.leaf (16)) (.branch 57 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 35 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 58 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 20 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-6)) (.leaf (-8)))) (.branch 33 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 39 (.leaf (-11)) (.branch 49 (.leaf (-13)) (.leaf (-14)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-28)) (.leaf (-31)))),
  (.branch 23 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-2))) (.branch 55 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 50 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 45 (.branch 33 (.leaf (-14)) (.branch 39 (.leaf (-13)) (.leaf (-12)))) (.branch 51 (.leaf (-11)) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 54 (.branch 18 (.leaf (-31)) (.branch 53 (.leaf (-30)) (.leaf (-25)))) (.branch 56 (.branch 55 (.leaf (-20)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5))))),
  (.branch 47 (.leaf (-2)) (.leaf (0))),
  (.branch 53 (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-18))) (.branch 51 (.leaf (-16)) (.branch 52 (.leaf (-14)) (.leaf (-12))))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))]
def witnessD7_026_292 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (4))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (2)))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (3)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (2)) (.branch 45 (.leaf (0)) (.leaf (1)))) (.branch 48 (.branch 47 (.leaf (5)) (.leaf (0))) (.branch 49 (.leaf (2)) (.leaf (4))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (2)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_292
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 43 (.branch 35 (.branch 31 (.leaf (7)) (.leaf (8))) (.branch 40 (.leaf (9)) (.leaf (10)))) (.branch 51 (.branch 46 (.leaf (11)) (.leaf (12))) (.branch 55 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 44 (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))) (.branch 54 (.branch 49 (.leaf (9)) (.leaf (10))) (.branch 58 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-10)) (.leaf (-11)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))) (.branch 43 (.branch 17 (.leaf (-18)) (.leaf (-25))) (.branch 46 (.leaf (-27)) (.leaf (-34))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (-31))) (.branch 47 (.leaf (-32)) (.leaf (-33)))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 49 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 53 (.leaf (-9)) (.branch 57 (.leaf (-8)) (.leaf (-5))))),
  (.branch 56 (.branch 47 (.leaf (-34)) (.leaf (-33))) (.branch 57 (.leaf (-28)) (.leaf (-23)))),
  (.leaf (0)),
  (.branch 55 (.branch 43 (.leaf (-8)) (.branch 54 (.leaf (-7)) (.leaf (-6)))) (.branch 56 (.leaf (-5)) (.branch 57 (.leaf (-4)) (.leaf (-3))))),
  (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-14))) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-8)) (.leaf (-6))) (.branch 57 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-33)) (.leaf (-30))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-24)) (.leaf (-21))))) (.branch 55 (.branch 53 (.leaf (-18)) (.branch 54 (.leaf (-15)) (.leaf (-12)))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 19 (.leaf (-4)) (.leaf (-3)))]
def witnessD7_026_293 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (5))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 41 (.branch 40 (.leaf (6)) (.leaf (1))) (.branch 42 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (2)) (.leaf (0))) (.branch 49 (.leaf (4)) (.leaf (1))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (5)) (.leaf (0))) (.branch 53 (.leaf (2)) (.leaf (3)))) (.branch 56 (.branch 55 (.leaf (1)) (.leaf (0))) (.branch 57 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_293
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 43 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 53 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 58 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 44 (.leaf (-25)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.leaf (-19)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (-10)) (.leaf (-13)))),
  (.branch 40 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 49 (.branch 45 (.leaf (-30)) (.leaf (-28))) (.branch 53 (.leaf (-26)) (.branch 57 (.leaf (-24)) (.leaf (-17))))),
  (.branch 51 (.branch 46 (.leaf (-20)) (.leaf (-19))) (.branch 56 (.leaf (-18)) (.branch 57 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-3)),
  (.branch 55 (.branch 47 (.leaf (-19)) (.leaf (-16))) (.branch 56 (.leaf (-12)) (.branch 57 (.leaf (-8)) (.leaf (-4))))),
  (.branch 53 (.branch 51 (.branch 50 (.leaf (-18)) (.leaf (-16))) (.branch 52 (.leaf (-14)) (.leaf (-12)))) (.branch 55 (.branch 54 (.leaf (-10)) (.leaf (-8))) (.branch 56 (.leaf (-6)) (.branch 57 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 54 (.branch 52 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 53 (.leaf (-11)) (.leaf (-10)))) (.branch 56 (.branch 55 (.leaf (-9)) (.leaf (-8))) (.branch 57 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))]
def witnessD7_026_294 : CycleWitness 7 where
  length := 58
  word := (.branch 29 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (1))))))) (.branch 43 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (5)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 41 (.branch 40 (.leaf (2)) (.leaf (0))) (.branch 42 (.leaf (6)) (.leaf (5)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (3)))) (.branch 48 (.branch 47 (.leaf (1)) (.leaf (0))) (.branch 49 (.leaf (4)) (.leaf (2))))) (.branch 54 (.branch 52 (.branch 51 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (3)) (.leaf (1)))) (.branch 56 (.branch 55 (.leaf (5)) (.leaf (0))) (.branch 57 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_294
  counts := ![(.branch 27 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 29 (.branch 15 (.branch 7 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 36 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.branch 58 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 46 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 57 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-23)))),
  (.branch 25 (.branch 7 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))) (.branch 39 (.branch 36 (.leaf (-3)) (.leaf (-4))) (.branch 54 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-25)))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 53 (.leaf (-15)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-43)) (.leaf (-46)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-13))) (.branch 43 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 49 (.branch 38 (.leaf (-23)) (.leaf (-22))) (.branch 53 (.leaf (-19)) (.branch 57 (.leaf (-16)) (.leaf (-8))))),
  (.branch 56 (.branch 55 (.leaf (-6)) (.leaf (-5))) (.branch 57 (.leaf (-4)) (.leaf (-3)))),
  (.branch 53 (.branch 51 (.branch 41 (.leaf (-25)) (.leaf (-24))) (.branch 52 (.leaf (-21)) (.leaf (-18)))) (.branch 55 (.branch 54 (.leaf (-15)) (.leaf (-12))) (.branch 56 (.leaf (-9)) (.branch 57 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-18))) (.branch 56 (.leaf (-16)) (.branch 57 (.leaf (-14)) (.leaf (-12))))),
  (.branch 53 (.branch 50 (.branch 15 (.leaf (-46)) (.leaf (-45))) (.branch 51 (.leaf (-40)) (.branch 52 (.leaf (-35)) (.leaf (-30))))) (.branch 55 (.branch 54 (.leaf (-25)) (.leaf (-20))) (.branch 56 (.leaf (-15)) (.branch 57 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 56 (.branch 44 (.leaf (-17)) (.leaf (-15))) (.branch 57 (.leaf (-10)) (.leaf (-5)))),
  (.branch 43 (.leaf (-3)) (.leaf (-2)))]
def witnessD7_026_295 : CycleWitness 7 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_295
  counts := ![(.branch 26 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 43 (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.branch 40 (.leaf (12)) (.leaf (13))))) (.branch 50 (.branch 46 (.leaf (14)) (.leaf (15))) (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 30 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 57 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 13 (.branch 10 (.leaf (-15)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 25 (.leaf (-10)) (.branch 36 (.leaf (-11)) (.leaf (-12))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 52 (.leaf (-7)) (.leaf (-8)))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))) (.branch 44 (.leaf (-3)) (.branch 55 (.leaf (-4)) (.leaf (-5))))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-12)) (.leaf (-6)))),
  (.branch 47 (.leaf (-9)) (.leaf (-6))),
  (.branch 52 (.branch 50 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9)))) (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 56 (.leaf (-5)) (.leaf (-4))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_026_296 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (5)))))) (.branch 42 (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (3)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_296
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.branch 26 (.leaf (18)) (.leaf (19))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (20)) (.leaf (21))) (.branch 31 (.leaf (22)) (.branch 33 (.leaf (23)) (.leaf (24))))) (.branch 37 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 38 (.leaf (27)) (.branch 40 (.leaf (28)) (.leaf (29)))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (30)) (.leaf (31))) (.branch 45 (.leaf (32)) (.branch 47 (.leaf (33)) (.leaf (34))))) (.branch 52 (.branch 50 (.leaf (35)) (.branch 51 (.leaf (36)) (.leaf (37)))) (.branch 54 (.leaf (38)) (.branch 55 (.leaf (39)) (.leaf (40)))))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.leaf (0))]
  high := ![(.branch 53 (.leaf (-6)) (.leaf (-5))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_026_297 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_297
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.branch 26 (.leaf (18)) (.leaf (19))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (20)) (.leaf (21))) (.branch 31 (.leaf (22)) (.branch 33 (.leaf (23)) (.leaf (24))))) (.branch 37 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 38 (.leaf (27)) (.branch 40 (.leaf (28)) (.leaf (29)))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (30)) (.leaf (31))) (.branch 45 (.leaf (32)) (.branch 47 (.leaf (33)) (.leaf (34))))) (.branch 52 (.branch 50 (.leaf (35)) (.branch 51 (.leaf (36)) (.leaf (37)))) (.branch 54 (.leaf (38)) (.branch 55 (.leaf (39)) (.leaf (40)))))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-45))),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 39 (.leaf (0)) (.leaf (-17))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 53 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-45)) (.leaf (-44))) (.branch 14 (.leaf (-43)) (.branch 15 (.leaf (-42)) (.leaf (-41))))) (.branch 19 (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38)))) (.branch 20 (.leaf (-37)) (.branch 21 (.leaf (-36)) (.leaf (-35)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-34)) (.leaf (-33))) (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30))))) (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.leaf (-26)) (.branch 32 (.leaf (-25)) (.leaf (-24))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_026_298 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_298
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.leaf (12)))) (.branch 23 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 32 (.leaf (20)) (.leaf (21)))) (.branch 37 (.branch 35 (.leaf (22)) (.leaf (23))) (.branch 38 (.leaf (24)) (.branch 40 (.leaf (25)) (.leaf (26)))))) (.branch 49 (.branch 44 (.branch 43 (.leaf (27)) (.leaf (28))) (.branch 46 (.leaf (29)) (.branch 47 (.leaf (30)) (.leaf (31))))) (.branch 52 (.branch 51 (.leaf (32)) (.leaf (33))) (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-8)))) (.branch 36 (.leaf (-10)) (.branch 50 (.leaf (-12)) (.leaf (-14))))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 48 (.leaf (-11)) (.leaf (-9))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_026_299 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_299
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 37 (.leaf (16)) (.leaf (17))))) (.branch 46 (.branch 43 (.leaf (18)) (.branch 44 (.leaf (19)) (.leaf (20)))) (.branch 51 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 14 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))) (.branch 42 (.branch 33 (.branch 31 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.branch 39 (.leaf (13)) (.leaf (14))))) (.branch 50 (.branch 45 (.leaf (15)) (.branch 47 (.leaf (16)) (.leaf (17)))) (.branch 53 (.leaf (18)) (.branch 56 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 4 (.leaf (-6)) (.branch 16 (.leaf (-7)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-10)))),
  (.branch 51 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 54 (.leaf (-1)) (.leaf (0)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_026_300 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (4)) (.leaf (0)))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 54 (.leaf (2)) (.branch 55 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_300
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 21 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 35 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 49 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-46))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 38 (.leaf (0)) (.leaf (-18))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 53 (.branch 51 (.leaf (-5)) (.branch 52 (.leaf (-4)) (.leaf (-3)))) (.branch 54 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-46)) (.leaf (-45))) (.branch 13 (.leaf (-44)) (.branch 14 (.leaf (-43)) (.leaf (-42))))) (.branch 18 (.branch 16 (.leaf (-41)) (.branch 17 (.leaf (-40)) (.leaf (-39)))) (.branch 19 (.leaf (-38)) (.branch 20 (.leaf (-37)) (.leaf (-36)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))) (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30))))) (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.leaf (-26)) (.branch 32 (.leaf (-25)) (.leaf (-24))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_026_301 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (2)) (.branch 49 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 54 (.leaf (3)) (.branch 55 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_301
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 21 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 35 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 49 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 53 (.branch 51 (.leaf (-5)) (.branch 52 (.leaf (-4)) (.leaf (-3)))) (.branch 54 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_026_302 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (2)) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 54 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_302
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 36 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 50 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-44))),
  (.branch 26 (.leaf (0)) (.leaf (-30))),
  (.branch 40 (.leaf (0)) (.leaf (-16))),
  (.branch 54 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-44)) (.leaf (-43))) (.branch 15 (.leaf (-42)) (.branch 16 (.leaf (-41)) (.leaf (-40))))) (.branch 20 (.branch 18 (.leaf (-39)) (.branch 19 (.leaf (-38)) (.leaf (-37)))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_026_303 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (6)) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 54 (.leaf (3)) (.branch 55 (.leaf (0)) (.leaf (1))))))))
  code := certificateD7_303
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 36 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 50 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 54 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 26 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-37))),
  (.branch 47 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 52 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20))))))) (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_026_304 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (0)))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (0)))) (.branch 47 (.leaf (3)) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 54 (.leaf (6)) (.branch 55 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_304
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 36 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 50 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-30))),
  (.branch 54 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.leaf (-6)) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_026_305 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (6)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (3))) (.branch 41 (.leaf (0)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (3))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_305
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 30 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))) (.branch 41 (.branch 30 (.leaf (-8)) (.leaf (-10))) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 43 (.leaf (-38)) (.leaf (-39)))),
  (.branch 15 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 53 (.branch 51 (.leaf (-5)) (.branch 52 (.leaf (-4)) (.leaf (-3)))) (.branch 54 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-5)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 46 (.branch 44 (.leaf (-39)) (.branch 45 (.leaf (-36)) (.leaf (-33)))) (.branch 47 (.leaf (-30)) (.branch 48 (.leaf (-27)) (.leaf (-24))))) (.branch 52 (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))]
def witnessD7_026 : Fin 17 → CycleWitness 7 := ![witnessD7_026_289, witnessD7_026_290, witnessD7_026_291, witnessD7_026_292, witnessD7_026_293, witnessD7_026_294, witnessD7_026_295, witnessD7_026_296, witnessD7_026_297, witnessD7_026_298, witnessD7_026_299, witnessD7_026_300, witnessD7_026_301, witnessD7_026_302, witnessD7_026_303, witnessD7_026_304, witnessD7_026_305]
end RealPinwheel.FiveSixths


