-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_031
-- name    : RealPinwheel_FiveSixths_WitnessD7_031
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:26.73546+00:00
-- url     : https://prove2.me/theorems/38b5e0cd-af94-4e99-8cc1-715871e56d8e
-- title:
--   Exact witness block D7_031
-- statement:
--   These exact witnesses represent words 377 through 395 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 377–395; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_031_376 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (0)))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 24 (.leaf (5)) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (0)))) (.branch 44 (.leaf (3)) (.branch 45 (.leaf (0)) (.leaf (1))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (4)) (.leaf (0)))) (.branch 50 (.leaf (6)) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_376
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (-4))) (.branch 50 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 48 (.branch 38 (.leaf (-19)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 43 (.branch 25 (.leaf (-32)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 51 (.leaf (-6)) (.leaf (-3)))]
def witnessD7_031_377 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (4)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (0)))) (.branch 44 (.leaf (6)) (.branch 45 (.leaf (1)) (.leaf (0))))) (.branch 49 (.branch 47 (.leaf (2)) (.branch 48 (.leaf (0)) (.leaf (1)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_377
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (12)) (.branch 28 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 43 (.branch 40 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 4 (.leaf (-10)) (.branch 15 (.leaf (-11)) (.leaf (-12))))) (.branch 30 (.branch 28 (.leaf (-13)) (.leaf (-14))) (.branch 41 (.leaf (-15)) (.branch 43 (.leaf (-16)) (.leaf (-17)))))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-34))),
  (.branch 44 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 44 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-12)))),
  (.branch 46 (.leaf (-2)) (.leaf (0))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.leaf (-31)))) (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.leaf (-27))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23)))) (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_031_378 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (6)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (3)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (6)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_378
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 28 (.leaf (-17)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-6)) (.branch 46 (.leaf (-7)) (.leaf (-8))))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 17 (.leaf (0)) (.branch 33 (.leaf (-1)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 45 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-16))))),
  (.branch 49 (.leaf (-3)) (.leaf (0))),
  (.branch 49 (.branch 47 (.leaf (-8)) (.branch 48 (.leaf (-7)) (.leaf (-6)))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 46 (.branch 26 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 44 (.leaf (-19)) (.branch 45 (.leaf (-17)) (.leaf (-15))))) (.branch 49 (.branch 47 (.leaf (-13)) (.branch 48 (.leaf (-11)) (.leaf (-9)))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-4)) (.leaf (-3))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_031_379 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (5))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (6))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (2)) (.leaf (1)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_379
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 49 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 46 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 28 (.leaf (-17)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))) (.branch 38 (.branch 25 (.leaf (-4)) (.leaf (-5))) (.branch 51 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-45))),
  (.branch 20 (.leaf (0)) (.leaf (-32))),
  (.branch 33 (.leaf (0)) (.leaf (-19))),
  (.branch 46 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 45 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-16))))),
  (.leaf (-7)),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-45)) (.leaf (-44))) (.branch 10 (.leaf (-43)) (.branch 11 (.leaf (-42)) (.leaf (-41))))) (.branch 15 (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38)))) (.branch 16 (.leaf (-37)) (.branch 17 (.leaf (-36)) (.leaf (-35)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-34)) (.leaf (-33))) (.branch 21 (.leaf (-32)) (.branch 22 (.leaf (-31)) (.leaf (-30))))) (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_031_380 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (5))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (4))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (1)))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (3)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (5)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (2)) (.leaf (4))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (1)))) (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_380
  counts := ![(.branch 24 (.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 28 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 28 (.leaf (-17)) (.branch 41 (.leaf (-20)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-25))) (.branch 43 (.leaf (-26)) (.leaf (-27)))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 45 (.branch 42 (.leaf (-23)) (.leaf (-22))) (.branch 48 (.leaf (-21)) (.branch 51 (.leaf (-20)) (.leaf (-16))))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 49 (.branch 31 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-27)) (.leaf (-24))) (.branch 46 (.leaf (-21)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-1)) (.leaf (0)))]
def witnessD7_031_381 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (1))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (3)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (0)))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (5)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (4)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_381
  counts := ![(.branch 24 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 28 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 42 (.branch 39 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 43 (.leaf (7)) (.branch 49 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-7)) (.leaf (-8))))) (.branch 39 (.branch 28 (.leaf (-9)) (.leaf (-12))) (.branch 42 (.leaf (-13)) (.branch 45 (.leaf (-14)) (.leaf (-15)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (-25))) (.branch 43 (.leaf (-28)) (.leaf (-29)))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-8)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-37)) (.leaf (-38)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (-10))) (.branch 48 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 46 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))),
  (.branch 50 (.branch 44 (.leaf (-29)) (.leaf (-27))) (.branch 51 (.leaf (-18)) (.leaf (-9)))),
  (.branch 18 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (0)))),
  (.branch 38 (.branch 31 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.leaf (-7)))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 23 (.leaf (-38)) (.branch 41 (.leaf (-36)) (.leaf (-33)))) (.branch 43 (.leaf (-30)) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessD7_031_382 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 36 (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_382
  counts := ![(.branch 25 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (11)) (.branch 28 (.leaf (12)) (.leaf (13)))) (.branch 33 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))) (.branch 46 (.branch 41 (.leaf (17)) (.branch 43 (.leaf (18)) (.leaf (19)))) (.branch 48 (.leaf (20)) (.branch 51 (.leaf (21)) (.leaf (22))))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 28 (.leaf (-26)) (.leaf (-34)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 44 (.leaf (-3)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 45 (.leaf (-9)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 39 (.branch 29 (.leaf (-34)) (.branch 34 (.leaf (-33)) (.leaf (-32)))) (.branch 44 (.leaf (-31)) (.branch 49 (.leaf (-30)) (.leaf (-25))))),
  (.branch 43 (.branch 36 (.leaf (-8)) (.leaf (-7))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 47 (.branch 45 (.leaf (-5)) (.branch 46 (.leaf (-4)) (.leaf (-3)))) (.branch 48 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 48 (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9)))) (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5))))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessD7_031_383 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (0)))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6))))))) (.branch 39 (.branch 33 (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (0)))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (6)) (.leaf (0)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (2))))) (.branch 49 (.branch 47 (.leaf (0)) (.branch 48 (.leaf (4)) (.leaf (0)))) (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_383
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 17 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 21 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 23 (.leaf (12)) (.leaf (13)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (14)) (.branch 28 (.leaf (15)) (.leaf (16)))) (.branch 34 (.branch 32 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 41 (.branch 40 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24)))) (.branch 49 (.branch 47 (.leaf (25)) (.leaf (26))) (.branch 51 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-7)))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (-9))) (.branch 42 (.leaf (-10)) (.leaf (-12))))]
  high := ![(.branch 46 (.branch 42 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))),
  (.branch 51 (.leaf (-4)) (.leaf (-2))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-14)) (.leaf (-13)))) (.branch 43 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-10))))) (.branch 48 (.branch 46 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.branch 49 (.leaf (-6)) (.leaf (-5))) (.branch 51 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 49 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))),
  (.branch 17 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-12)) (.leaf (-11))) (.branch 45 (.leaf (-10)) (.branch 46 (.leaf (-9)) (.leaf (-8))))) (.branch 49 (.branch 48 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3))))))]
def witnessD7_031_384 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_384
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 28 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-43))),
  (.branch 35 (.leaf (0)) (.leaf (-17))),
  (.branch 48 (.leaf (0)) (.leaf (-4))),
  (.branch 22 (.leaf (0)) (.leaf (-30)))]
  high := ![(.branch 48 (.leaf (-12)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.branch 44 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-2)) (.leaf (0))))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.branch 30 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-43)) (.leaf (-42))) (.branch 12 (.leaf (-41)) (.branch 13 (.leaf (-40)) (.leaf (-39))))) (.branch 16 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_031_385 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (3)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_385
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 39 (.branch 30 (.branch 28 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 41 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 49 (.leaf (18)) (.branch 52 (.leaf (19)) (.leaf (20))))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 43 (.leaf (-6)) (.leaf (-7))))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 48 (.leaf (-12)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 47 (.branch 44 (.leaf (-7)) (.leaf (-6))) (.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-2)) (.leaf (0))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_031_386 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (6)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_386
  counts := ![(.branch 23 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 43 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 49 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 43 (.leaf (-4)) (.leaf (-5))))),
  (.branch 20 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))) (.branch 40 (.branch 30 (.leaf (-9)) (.leaf (-10))) (.branch 46 (.leaf (-11)) (.leaf (-13))))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 50 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.leaf (-13)) (.branch 51 (.leaf (-12)) (.leaf (-10)))),
  (.branch 39 (.branch 32 (.leaf (-7)) (.leaf (-6))) (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-2)) (.leaf (0))))),
  (.branch 46 (.branch 43 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 34 (.leaf (-5)) (.leaf (-3))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_031_387 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 38 (.leaf (2)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_387
  counts := ![(.branch 24 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 50 (.leaf (23)) (.leaf (24))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 9 (.branch 7 (.leaf (-9)) (.leaf (-10))) (.branch 11 (.leaf (-11)) (.leaf (-12))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-28)) (.leaf (-29)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (-1))) (.branch 51 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 51 (.leaf (-12)) (.leaf (-6))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 39 (.leaf (-16)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 47 (.branch 44 (.branch 26 (.leaf (-29)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_031_388 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (2))) (.branch 51 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_388
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 51 (.leaf (23)) (.leaf (24))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 7 (.leaf (-9)) (.branch 9 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 49 (.leaf (-11)) (.leaf (-6))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 44 (.leaf (-5)) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_031_389 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_389
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 49 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 51 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 47 (.leaf (-10)) (.leaf (-6))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0)))]
def witnessD7_031_390 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_390
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 31 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 44 (.branch 40 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))) (.branch 31 (.branch 18 (.leaf (-9)) (.leaf (-10))) (.branch 44 (.leaf (-11)) (.leaf (-12))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-29))),
  (.branch 49 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 48 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 50 (.branch 49 (.leaf (-20)) (.leaf (-15))) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.leaf (-7)) (.leaf (-5))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 30 (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23))))) (.branch 33 (.branch 31 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_031_391 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 38 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (4)) (.leaf (0)))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (6)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_391
  counts := ![(.branch 24 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 44 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 25 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 45 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 46 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 25 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-6)))) (.branch 31 (.branch 28 (.leaf (-7)) (.leaf (-8))) (.branch 40 (.leaf (-9)) (.branch 51 (.leaf (-12)) (.leaf (-13)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 42 (.leaf (-12)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.branch 33 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 45 (.branch 42 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))))),
  (.leaf (-13)),
  (.branch 50 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 47 (.branch 44 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.leaf (-2)) (.leaf (0))),
  (.branch 42 (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_031_392 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (4)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_392
  counts := ![(.branch 24 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 37 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 34 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 42 (.leaf (16)) (.leaf (17)))) (.branch 47 (.leaf (18)) (.branch 50 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-29))),
  (.branch 49 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 48 (.leaf (-12)) (.branch 51 (.leaf (-10)) (.leaf (-5)))),
  (.branch 45 (.leaf (-6)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 30 (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23))))) (.branch 33 (.branch 31 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_031_393 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (6)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (5)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_393
  counts := ![(.branch 24 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 44 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 31 (.leaf (-19)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-6)) (.leaf (-8)))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 39 (.branch 33 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 45 (.branch 42 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 41 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3)))]
def witnessD7_031_394 : CycleWitness 7 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (2)) (.leaf (1))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (5))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (6))) (.branch 51 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_394
  counts := ![(.branch 23 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 29 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 32 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 52 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 31 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 45 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 29 (.leaf (-11)) (.leaf (-13)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-5)))) (.branch 34 (.branch 28 (.leaf (-6)) (.leaf (-7))) (.branch 44 (.leaf (-9)) (.leaf (-10))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (-1)) (.leaf (-4)))) (.branch 35 (.leaf (-6)) (.branch 45 (.leaf (-7)) (.leaf (-9))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7)))),
  (.branch 49 (.branch 45 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-5)) (.leaf (-3))))),
  (.branch 46 (.leaf (-9)) (.leaf (-8))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_031 : Fin 19 → CycleWitness 7 := ![witnessD7_031_376, witnessD7_031_377, witnessD7_031_378, witnessD7_031_379, witnessD7_031_380, witnessD7_031_381, witnessD7_031_382, witnessD7_031_383, witnessD7_031_384, witnessD7_031_385, witnessD7_031_386, witnessD7_031_387, witnessD7_031_388, witnessD7_031_389, witnessD7_031_390, witnessD7_031_391, witnessD7_031_392, witnessD7_031_393, witnessD7_031_394]
end RealPinwheel.FiveSixths


