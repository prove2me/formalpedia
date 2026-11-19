-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_168
-- name    : RealPinwheel_FiveSixths_WitnessD8_168
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:23:20.136919+00:00
-- url     : https://prove2.me/theorems/64a3d12f-cf59-4032-a637-def86153e330
-- title:
--   Exact witness block D8_168
-- statement:
--   These exact witnesses represent words 1600 through 1616 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1600–1616; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_168_1599 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (5)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1599
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 8 (.leaf (-4)) (.leaf (-5)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 25 (.leaf (-14)) (.leaf (-15)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-10))) (.branch 45 (.leaf (-15)) (.leaf (-19)))),
  (.branch 23 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.leaf (0))]
  high := ![(.branch 47 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5))))),
  (.branch 51 (.leaf (-5)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-19)) (.leaf (-18))) (.branch 48 (.leaf (-17)) (.branch 49 (.leaf (-16)) (.leaf (-15))))) (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_168_1600 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (3)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (6)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_1600
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 45 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 56 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-43))),
  (.branch 27 (.leaf (0)) (.leaf (-29))),
  (.branch 41 (.leaf (0)) (.leaf (-15))),
  (.branch 55 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 55 (.leaf (-4)) (.leaf (-2))),
  (.branch 53 (.leaf (-1)) (.leaf (0))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-43)) (.leaf (-42))) (.branch 16 (.leaf (-41)) (.branch 17 (.leaf (-40)) (.leaf (-39))))) (.branch 20 (.branch 19 (.leaf (-38)) (.leaf (-37))) (.branch 21 (.leaf (-36)) (.branch 22 (.leaf (-35)) (.leaf (-34)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29))))) (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.leaf (-25)) (.branch 33 (.leaf (-24)) (.leaf (-23))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 34 (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 32 (.branch 31 (.leaf (-26)) (.leaf (-25))) (.branch 33 (.leaf (-24)) (.leaf (-23))))) (.branch 37 (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_168_1601 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (6)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (3)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (5)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (7)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1601
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.leaf (-4)) (.branch 52 (.leaf (-3)) (.leaf (-2)))),
  (.branch 50 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_168_1602 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (7)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (7)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1602
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 39 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 53 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-9)))) (.branch 39 (.leaf (-10)) (.branch 48 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 47 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5))))),
  (.branch 55 (.leaf (-4)) (.leaf (-2))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 51 (.leaf (-10)) (.leaf (-9)))) (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 50 (.branch 47 (.branch 26 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))),
  (.branch 46 (.branch 41 (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16))))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_168_1603 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (5))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (4)) (.leaf (7))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (5)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (4)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_1603
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 49 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-35))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.leaf (-4)) (.branch 52 (.leaf (-3)) (.leaf (-2)))),
  (.branch 52 (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 49 (.branch 46 (.branch 8 (.leaf (-35)) (.branch 27 (.leaf (-34)) (.leaf (-33)))) (.branch 47 (.leaf (-30)) (.branch 48 (.leaf (-27)) (.leaf (-24))))) (.branch 52 (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 36 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_168_1604 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (0)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (7)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (1))) (.branch 55 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1604
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 41 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 55 (.leaf (19)) (.leaf (20))))))),
  (.branch 26 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-36))),
  (.branch 48 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 47 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5))))),
  (.branch 55 (.leaf (-4)) (.leaf (-2))),
  (.branch 54 (.branch 46 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-36)) (.leaf (-35))) (.branch 23 (.leaf (-34)) (.leaf (-33)))) (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_168_1605 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (5)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (6)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (5)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1605
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 54 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 33 (.branch 30 (.leaf (7)) (.leaf (8))) (.branch 37 (.leaf (9)) (.leaf (10)))) (.branch 49 (.branch 45 (.leaf (11)) (.leaf (12))) (.branch 53 (.leaf (13)) (.leaf (14)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.leaf (7))))),
  (.branch 31 (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 51 (.branch 47 (.leaf (-6)) (.leaf (-5))) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.leaf (-1)) (.leaf (0))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_168_1606 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (7)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (6)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (5)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (7)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (3)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_1606
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 47 (.branch 24 (.leaf (-5)) (.leaf (-6))) (.branch 52 (.leaf (-7)) (.leaf (-8))))),
  (.branch 28 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 38 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 53 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 53 (.branch 39 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5))))),
  (.branch 47 (.branch 46 (.leaf (-3)) (.leaf (-2))) (.branch 48 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_168_1607 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (7)) (.leaf (4))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (3)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (7)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (1)) (.leaf (6)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (7)) (.leaf (3))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (5))) (.branch 55 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_1607
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-18)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-31)) (.leaf (-32)))) (.branch 38 (.leaf (-33)) (.branch 49 (.leaf (-34)) (.leaf (-35))))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 54 (.leaf (-15)) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 50 (.leaf (-35)) (.branch 51 (.leaf (-30)) (.leaf (-25)))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_168_1608 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (7)) (.branch 37 (.leaf (0)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (6)) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1608
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-14)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.branch 50 (.leaf (-6)) (.leaf (-7)))),
  (.branch 36 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 52 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 48 (.branch 44 (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.leaf (-10))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 51 (.branch 48 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessD8_168_1609 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (7)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (5)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (6))) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (5)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1609
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 44 (.leaf (14)) (.leaf (15))) (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 30 (.leaf (5)) (.branch 34 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 49 (.leaf (8)) (.branch 55 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 16 (.leaf (-17)) (.branch 44 (.leaf (-20)) (.leaf (-22))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 34 (.leaf (-22)) (.leaf (-25)))),
  (.branch 3 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-10))) (.branch 45 (.leaf (-13)) (.leaf (-15)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (-2))) (.branch 53 (.leaf (-5)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (-26)) (.leaf (-28)))),
  (.leaf (0))]
  high := ![(.branch 45 (.leaf (-22)) (.branch 55 (.leaf (-18)) (.leaf (-11)))),
  (.branch 47 (.branch 35 (.leaf (-25)) (.branch 41 (.leaf (-24)) (.leaf (-23)))) (.branch 54 (.branch 53 (.leaf (-22)) (.leaf (-18))) (.branch 55 (.leaf (-14)) (.leaf (-10))))),
  (.branch 38 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 44 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10))))),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 48 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-11))))) (.branch 53 (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 51 (.branch 48 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 49 (.leaf (-24)) (.branch 50 (.leaf (-21)) (.leaf (-18))))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-12))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0))]
def witnessD8_168_1610 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (1)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (3))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (7))) (.branch 55 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1610
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 54 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-30))),
  (.branch 54 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.leaf (-20)))) (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))))) (.branch 48 (.branch 44 (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_168_1611 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (6)) (.leaf (5))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (7)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (5)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (4)) (.leaf (3))))) (.branch 52 (.branch 50 (.leaf (1)) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1611
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (7)) (.leaf (8))) (.branch 38 (.leaf (9)) (.leaf (10)))) (.branch 50 (.branch 46 (.leaf (11)) (.leaf (12))) (.branch 54 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 25 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))) (.branch 32 (.leaf (-19)) (.branch 53 (.leaf (-20)) (.leaf (-23))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 44 (.leaf (-18)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (-10))) (.branch 45 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.leaf (-23)) (.branch 55 (.leaf (-18)) (.leaf (-13)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.branch 45 (.leaf (-22)) (.leaf (-20))) (.branch 54 (.leaf (-17)) (.branch 55 (.leaf (-14)) (.leaf (-11))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 49 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD8_168_1612 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (4)) (.leaf (7))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (2))) (.branch 41 (.leaf (1)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (5)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (7)) (.leaf (4))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (2))) (.branch 55 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_1612
  counts := ![(.branch 25 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 47 (.leaf (8)) (.branch 51 (.leaf (9)) (.leaf (10)))))),
  (.branch 26 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-5)) (.branch 51 (.leaf (-7)) (.leaf (-9))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 31 (.leaf (-7)) (.branch 45 (.leaf (-9)) (.leaf (-11))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-7))) (.branch 42 (.leaf (-10)) (.leaf (-11)))),
  (.branch 27 (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-31)) (.leaf (-32)))) (.branch 38 (.leaf (-33)) (.branch 49 (.leaf (-34)) (.leaf (-35))))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 37 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 54 (.leaf (-6)) (.branch 55 (.leaf (-4)) (.leaf (-2)))),
  (.branch 53 (.branch 52 (.leaf (-9)) (.leaf (-8))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5))))),
  (.branch 46 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 53 (.branch 43 (.leaf (-11)) (.leaf (-10))) (.branch 54 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 52 (.branch 50 (.leaf (-35)) (.branch 51 (.leaf (-30)) (.leaf (-25)))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-15))) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 38 (.leaf (-1)) (.leaf (0))),
  (.branch 51 (.branch 49 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.leaf (-7)))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_168_1613 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (7)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (5)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_1613
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14))))) (.branch 49 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 28 (.branch 19 (.leaf (0)) (.leaf (-1))) (.branch 47 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 33 (.leaf (-6)) (.branch 42 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.branch 45 (.leaf (-32)) (.leaf (-33)))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 55 (.leaf (-10)) (.leaf (-5))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 32 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 48 (.leaf (-3)) (.leaf (-2))) (.branch 50 (.leaf (-1)) (.leaf (0)))),
  (.branch 54 (.branch 43 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-33)) (.leaf (-30))) (.branch 48 (.leaf (-27)) (.branch 49 (.leaf (-24)) (.leaf (-21))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 18 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))]
def witnessD8_168_1614 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (4)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (7))) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (0)) (.leaf (2)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_1614
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 43 (.leaf (15)) (.branch 46 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 42 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 50 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-37))),
  (.branch 47 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 52 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20))))))) (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_168_1615 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (2)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (3))) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (7))) (.branch 48 (.leaf (2)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (3)) (.leaf (4)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (2))) (.branch 55 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1615
  counts := ![(.branch 27 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 32 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 43 (.leaf (12)) (.leaf (13))) (.branch 50 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 31 (.leaf (5)) (.branch 37 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 28 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 34 (.leaf (5)) (.branch 40 (.leaf (6)) (.leaf (7)))) (.branch 51 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 18 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.leaf (-5)))) (.branch 32 (.branch 29 (.leaf (-6)) (.leaf (-7))) (.branch 43 (.leaf (-8)) (.branch 46 (.leaf (-9)) (.leaf (-10)))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 19 (.leaf (0)) (.leaf (-37))),
  (.branch 47 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 51 (.leaf (-10)) (.leaf (-9))),
  (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 49 (.branch 43 (.leaf (-14)) (.leaf (-12))) (.branch 55 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.branch 24 (.leaf (-33)) (.leaf (-32))) (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.branch 36 (.leaf (-21)) (.leaf (-20))))))) (.branch 46 (.branch 41 (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-18))) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-14))) (.branch 44 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-11)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_168 : Fin 17 → CycleWitness 8 := ![witnessD8_168_1599, witnessD8_168_1600, witnessD8_168_1601, witnessD8_168_1602, witnessD8_168_1603, witnessD8_168_1604, witnessD8_168_1605, witnessD8_168_1606, witnessD8_168_1607, witnessD8_168_1608, witnessD8_168_1609, witnessD8_168_1610, witnessD8_168_1611, witnessD8_168_1612, witnessD8_168_1613, witnessD8_168_1614, witnessD8_168_1615]
end RealPinwheel.FiveSixths


