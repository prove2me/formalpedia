-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_142
-- name    : RealPinwheel_FiveSixths_WitnessD8_142
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:01:58.180939+00:00
-- url     : https://prove2.me/theorems/5f2a389f-4bbf-47fe-8c36-2e246cf5787d
-- title:
--   Exact witness block D8_142
-- statement:
--   These exact witnesses represent words 1187 through 1201 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1187–1201; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_142_1186 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (5)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (0))) (.branch 52 (.leaf (6)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (7))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (1)) (.leaf (5)))))))))
  code := certificateD8_1186
  counts := ![(.branch 32 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 57 (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18)))) (.branch 60 (.leaf (19)) (.branch 64 (.leaf (20)) (.leaf (21))))))),
  (.branch 34 (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))) (.branch 49 (.branch 40 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.branch 46 (.leaf (14)) (.leaf (15))))) (.branch 59 (.branch 53 (.leaf (16)) (.branch 56 (.leaf (17)) (.leaf (18)))) (.branch 62 (.leaf (19)) (.branch 65 (.leaf (20)) (.leaf (21))))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.branch 61 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 13 (.branch 10 (.leaf (-17)) (.leaf (-18))) (.branch 16 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-21)) (.leaf (-22)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 61 (.leaf (-20)) (.branch 65 (.leaf (-14)) (.leaf (-7)))),
  (.branch 50 (.leaf (-9)) (.leaf (-7))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 63 (.branch 45 (.leaf (-11)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_142_1187 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (5))) (.branch 40 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (2)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (4)))))))))
  code := certificateD8_1187
  counts := ![(.branch 32 (.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 26 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))))) (.branch 48 (.branch 40 (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14)))) (.branch 43 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17))))) (.branch 56 (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20)))) (.branch 62 (.branch 59 (.leaf (21)) (.leaf (22))) (.branch 65 (.leaf (23)) (.leaf (24))))))),
  (.branch 31 (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 30 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 60 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 63 (.leaf (-5)) (.leaf (-4)))),
  (.branch 61 (.leaf (-7)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 52 (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_142_1188 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (3)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (1))) (.branch 40 (.leaf (6)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (4))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (7)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (1)) (.leaf (3)))))))))
  code := certificateD8_1188
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 14 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 47 (.leaf (12)) (.leaf (13))))) (.branch 58 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 64 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1))),
  (.branch 62 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 27 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 16 (.leaf (-3)) (.leaf (-4)))) (.branch 49 (.branch 38 (.leaf (-5)) (.leaf (-6))) (.branch 60 (.leaf (-7)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-48))),
  (.branch 40 (.leaf (0)) (.leaf (-26))),
  (.branch 62 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-5)) (.branch 62 (.leaf (-4)) (.leaf (-3)))),
  (.branch 65 (.leaf (-8)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-48)) (.branch 20 (.leaf (-47)) (.leaf (-46)))) (.branch 22 (.leaf (-45)) (.branch 23 (.leaf (-44)) (.leaf (-43))))) (.branch 27 (.branch 25 (.leaf (-42)) (.branch 26 (.leaf (-41)) (.leaf (-40)))) (.branch 28 (.leaf (-39)) (.branch 29 (.leaf (-38)) (.leaf (-37)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-36)) (.branch 32 (.leaf (-35)) (.leaf (-34)))) (.branch 34 (.leaf (-33)) (.branch 35 (.leaf (-32)) (.leaf (-31))))) (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25))))))) (.branch 54 (.branch 48 (.branch 45 (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22)))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19))))) (.branch 51 (.branch 49 (.leaf (-18)) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))))) (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 53 (.branch 46 (.branch 43 (.branch 41 (.leaf (-26)) (.branch 42 (.leaf (-25)) (.leaf (-24)))) (.branch 44 (.leaf (-23)) (.branch 45 (.leaf (-22)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-20)) (.branch 48 (.leaf (-19)) (.leaf (-18)))) (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))))) (.branch 59 (.branch 56 (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))) (.branch 57 (.leaf (-10)) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_142_1189 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (6)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (3)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (6)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (4))) (.branch 56 (.leaf (3)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (2))) (.branch 60 (.leaf (0)) (.leaf (7)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (3))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (4)))))))))
  code := certificateD8_1189
  counts := ![(.branch 32 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 16 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 38 (.branch 36 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 58 (.branch 51 (.leaf (16)) (.branch 54 (.leaf (17)) (.leaf (18)))) (.branch 60 (.leaf (19)) (.branch 64 (.leaf (20)) (.leaf (21))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 37 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 59 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 34 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 41 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 63 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 50 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 61 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.leaf (-15)))) (.branch 38 (.branch 16 (.leaf (-16)) (.leaf (-18))) (.branch 60 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 47 (.leaf (-10)) (.leaf (-12)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 17 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 61 (.leaf (-20)) (.branch 65 (.leaf (-15)) (.leaf (-9)))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 54 (.branch 48 (.leaf (-12)) (.leaf (-11))) (.branch 60 (.leaf (-10)) (.leaf (-9)))),
  (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 52 (.branch 45 (.branch 42 (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 43 (.leaf (-24)) (.branch 44 (.leaf (-23)) (.leaf (-22))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-20)) (.leaf (-19)))) (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))))) (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_142_1190 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (7))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (6)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (4)) (.leaf (1))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (1))) (.branch 44 (.leaf (7)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (4)) (.leaf (6))) (.branch 56 (.leaf (1)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (3)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (0))) (.branch 64 (.leaf (2)) (.branch 65 (.leaf (1)) (.leaf (7)))))))))
  code := certificateD8_1190
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))) (.branch 47 (.branch 39 (.branch 35 (.leaf (8)) (.leaf (9))) (.branch 43 (.leaf (10)) (.leaf (11)))) (.branch 56 (.branch 51 (.leaf (12)) (.leaf (13))) (.branch 60 (.leaf (14)) (.branch 65 (.leaf (15)) (.leaf (16))))))),
  (.branch 31 (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 48 (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 40 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.branch 62 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3)))),
  (.branch 44 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 66 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))) (.branch 37 (.leaf (-22)) (.branch 59 (.leaf (-24)) (.leaf (-28))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.branch 14 (.leaf (-9)) (.leaf (-10))))) (.branch 43 (.branch 35 (.leaf (-11)) (.branch 39 (.leaf (-12)) (.leaf (-13)))) (.branch 47 (.leaf (-14)) (.branch 51 (.leaf (-15)) (.leaf (-16)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 52 (.leaf (-17)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (-23)) (.leaf (-24)))),
  (.branch 13 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 64 (.branch 60 (.leaf (-28)) (.leaf (-27))) (.branch 65 (.leaf (-22)) (.leaf (-17)))),
  (.branch 52 (.leaf (-16)) (.branch 61 (.leaf (-15)) (.leaf (-13)))),
  (.branch 59 (.branch 53 (.leaf (-20)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-11)))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-24)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 60 (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_142_1191 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (7))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (5))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (0)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.leaf (5)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (6)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (3))) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (0))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (0))) (.branch 56 (.leaf (3)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (0)) (.leaf (4))) (.branch 60 (.leaf (2)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (5)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (3)) (.leaf (6)))))))))
  code := certificateD8_1191
  counts := ![(.branch 33 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 17 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 26 (.leaf (8)) (.branch 29 (.leaf (9)) (.leaf (10)))))) (.branch 48 (.branch 39 (.branch 36 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.branch 45 (.leaf (14)) (.leaf (15))))) (.branch 58 (.branch 51 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18)))) (.branch 61 (.leaf (19)) (.branch 64 (.leaf (20)) (.leaf (21))))))),
  (.branch 30 (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 52 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 31 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 53 (.leaf (7)) (.branch 60 (.leaf (8)) (.leaf (9)))))),
  (.branch 34 (.branch 12 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 37 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 49 (.leaf (3)) (.branch 62 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 15 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 66 (.leaf (4)) (.leaf (5))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 31 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 16 (.leaf (-7)) (.leaf (-8)))) (.branch 53 (.branch 38 (.leaf (-9)) (.leaf (-10))) (.branch 60 (.leaf (-11)) (.leaf (-12))))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (-3))) (.branch 65 (.leaf (-5)) (.leaf (-7)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 44 (.leaf (-10)) (.leaf (-12)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (-4))) (.branch 49 (.leaf (-6)) (.branch 62 (.leaf (-7)) (.leaf (-8))))),
  (.branch 27 (.leaf (0)) (.branch 40 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 52 (.leaf (-17)) (.branch 65 (.leaf (-14)) (.leaf (-7)))),
  (.branch 64 (.branch 58 (.leaf (-7)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10)))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 62 (.branch 60 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 61 (.leaf (-10)) (.leaf (-9)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5))))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-7))) (.branch 65 (.leaf (-6)) (.leaf (-5)))),
  (.branch 55 (.leaf (-2)) (.branch 56 (.leaf (-1)) (.leaf (0)))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_142_1192 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (0))) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (5))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (4)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (7)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (4))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (6)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (5))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (6))) (.branch 60 (.leaf (3)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (4)) (.leaf (7)))))))))
  code := certificateD8_1192
  counts := ![(.branch 31 (.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))) (.branch 47 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 51 (.leaf (15)) (.branch 54 (.leaf (16)) (.leaf (17)))) (.branch 61 (.leaf (18)) (.branch 64 (.leaf (19)) (.leaf (20))))))),
  (.branch 30 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 45 (.leaf (9)) (.leaf (10)))) (.branch 58 (.branch 53 (.leaf (11)) (.leaf (12))) (.branch 63 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 60 (.leaf (4)) (.leaf (5))))),
  (.branch 39 (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 52 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 59 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.branch 66 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-23)) (.leaf (-26)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 48 (.leaf (-26)) (.leaf (-31)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-18))) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (-15))) (.branch 32 (.leaf (-16)) (.leaf (-17)))),
  (.branch 39 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 52 (.leaf (-3)) (.branch 65 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 48 (.branch 38 (.leaf (-26)) (.leaf (-25))) (.branch 58 (.leaf (-24)) (.branch 65 (.leaf (-20)) (.leaf (-10))))),
  (.branch 59 (.branch 49 (.leaf (-31)) (.branch 54 (.leaf (-30)) (.leaf (-29)))) (.branch 64 (.leaf (-28)) (.branch 65 (.leaf (-22)) (.leaf (-16))))),
  (.branch 64 (.branch 63 (.leaf (-20)) (.leaf (-15))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.branch 47 (.branch 33 (.leaf (-17)) (.leaf (-16))) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 60 (.branch 57 (.branch 39 (.leaf (-23)) (.branch 56 (.leaf (-22)) (.leaf (-20)))) (.branch 58 (.leaf (-18)) (.branch 59 (.leaf (-16)) (.leaf (-14))))) (.branch 63 (.branch 61 (.leaf (-12)) (.branch 62 (.leaf (-10)) (.leaf (-8)))) (.branch 64 (.leaf (-6)) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_142_1193 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (5)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (7)) (.leaf (3))) (.branch 40 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (6)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (5)) (.leaf (3))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (0))) (.branch 60 (.leaf (7)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (1)) (.leaf (0))) (.branch 64 (.leaf (3)) (.branch 65 (.leaf (5)) (.leaf (4)))))))))
  code := certificateD8_1193
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 29 (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 46 (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 62 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 31 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 47 (.branch 39 (.leaf (4)) (.leaf (5))) (.branch 55 (.leaf (6)) (.branch 64 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 50 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 58 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 32 (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 54 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 60 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-21)) (.leaf (-22)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 63 (.branch 45 (.leaf (-22)) (.branch 62 (.leaf (-20)) (.leaf (-16)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 56 (.leaf (-11)) (.branch 65 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (-17)) (.leaf (-16))) (.branch 52 (.leaf (-15)) (.leaf (-14)))) (.branch 55 (.branch 54 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-11)) (.leaf (-10))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_142_1194 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (7)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (6))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (1)) (.leaf (7))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (2))) (.branch 44 (.leaf (1)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (2)) (.leaf (1)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (4)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (1))) (.branch 60 (.leaf (5)) (.leaf (0)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (7))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (0)) (.leaf (4)))))))))
  code := certificateD8_1194
  counts := ![(.branch 32 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 53 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 31 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))) (.branch 49 (.branch 40 (.branch 35 (.leaf (7)) (.leaf (8))) (.branch 44 (.leaf (9)) (.leaf (10)))) (.branch 59 (.branch 54 (.leaf (11)) (.leaf (12))) (.branch 64 (.leaf (13)) (.leaf (14)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 36 (.leaf (5)) (.branch 43 (.leaf (6)) (.leaf (7)))) (.branch 55 (.leaf (8)) (.branch 62 (.leaf (9)) (.leaf (10)))))),
  (.branch 25 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 37 (.leaf (3)) (.leaf (4))) (.branch 58 (.leaf (5)) (.leaf (6))))),
  (.branch 33 (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 56 (.branch 45 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 51 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 41 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 63 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 34 (.leaf (-11)) (.leaf (-14)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 44 (.leaf (-13)) (.leaf (-14)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-15))) (.branch 48 (.leaf (-21)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 27 (.branch 6 (.leaf (0)) (.leaf (-11))) (.branch 60 (.leaf (-15)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 54 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 58 (.leaf (-12)) (.branch 62 (.leaf (-11)) (.leaf (-10))))),
  (.branch 55 (.branch 45 (.leaf (-14)) (.branch 50 (.leaf (-13)) (.leaf (-12)))) (.branch 60 (.leaf (-11)) (.branch 65 (.leaf (-10)) (.leaf (-6))))),
  (.branch 63 (.branch 49 (.leaf (-24)) (.branch 56 (.leaf (-23)) (.leaf (-22)))) (.branch 64 (.leaf (-18)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 63 (.branch 61 (.leaf (-18)) (.branch 62 (.leaf (-16)) (.leaf (-14)))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-10)) (.leaf (-8))))),
  (.branch 59 (.branch 55 (.branch 53 (.leaf (-14)) (.branch 54 (.leaf (-13)) (.leaf (-12)))) (.branch 57 (.branch 56 (.leaf (-11)) (.leaf (-10))) (.branch 58 (.leaf (-9)) (.leaf (-8))))) (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_142_1195 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (7))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (4)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (7)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (4)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (0)) (.leaf (6))) (.branch 44 (.leaf (3)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (5)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (3)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (0))) (.branch 56 (.leaf (2)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (0))) (.branch 60 (.leaf (5)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (1))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (6)) (.leaf (3)))))))))
  code := certificateD8_1195
  counts := ![(.branch 31 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 46 (.branch 38 (.branch 34 (.leaf (8)) (.leaf (9))) (.branch 42 (.leaf (10)) (.leaf (11)))) (.branch 55 (.branch 50 (.leaf (12)) (.leaf (13))) (.branch 59 (.leaf (14)) (.branch 64 (.leaf (15)) (.leaf (16))))))),
  (.branch 30 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 57 (.branch 51 (.leaf (9)) (.leaf (10))) (.branch 63 (.leaf (11)) (.leaf (12)))))),
  (.branch 33 (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 56 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 36 (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))) (.branch 52 (.branch 44 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 66 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 53 (.leaf (6)) (.branch 61 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 49 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 60 (.leaf (5)) (.leaf (6))))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 65 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 54 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.branch 13 (.leaf (-12)) (.leaf (-13))))) (.branch 42 (.branch 34 (.leaf (-14)) (.branch 38 (.leaf (-15)) (.leaf (-16)))) (.branch 46 (.leaf (-17)) (.branch 50 (.leaf (-18)) (.leaf (-19)))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 51 (.leaf (-22)) (.leaf (-25)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 62 (.leaf (-10)) (.leaf (-11)))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-2)) (.branch 58 (.leaf (-3)) (.leaf (-4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-17))) (.branch 20 (.leaf (-18)) (.branch 28 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 60 (.branch 51 (.leaf (-19)) (.leaf (-18))) (.branch 65 (.leaf (-16)) (.leaf (-13)))),
  (.branch 58 (.branch 52 (.leaf (-25)) (.leaf (-23))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-16)) (.leaf (-11))))),
  (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5)))),
  (.branch 59 (.leaf (-4)) (.branch 60 (.leaf (-2)) (.leaf (0)))),
  (.branch 63 (.branch 62 (.leaf (-20)) (.leaf (-16))) (.branch 64 (.leaf (-12)) (.branch 65 (.leaf (-8)) (.leaf (-4))))),
  (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 60 (.branch 57 (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))) (.branch 58 (.leaf (-9)) (.branch 59 (.leaf (-8)) (.leaf (-7))))) (.branch 63 (.branch 61 (.leaf (-6)) (.branch 62 (.leaf (-5)) (.leaf (-4)))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_142_1196 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (1)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (1)) (.leaf (2)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (1))) (.branch 40 (.leaf (7)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (5))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (6))) (.branch 52 (.leaf (0)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (1))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (4)) (.leaf (0))) (.branch 60 (.leaf (2)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (7)) (.leaf (0))) (.branch 64 (.leaf (5)) (.branch 65 (.leaf (1)) (.leaf (2)))))))))
  code := certificateD8_1196
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 32 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))) (.branch 50 (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.branch 46 (.leaf (12)) (.leaf (13))))) (.branch 57 (.branch 54 (.leaf (14)) (.leaf (15))) (.branch 61 (.leaf (16)) (.branch 65 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))) (.branch 49 (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))) (.branch 60 (.branch 55 (.leaf (9)) (.leaf (10))) (.branch 66 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 58 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.branch 64 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3)))),
  (.branch 40 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 62 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 58 (.leaf (-5)) (.branch 62 (.leaf (-4)) (.leaf (-3)))),
  (.branch 61 (.leaf (-1)) (.leaf (0))),
  (.branch 59 (.branch 55 (.branch 37 (.leaf (-27)) (.branch 54 (.leaf (-26)) (.leaf (-24)))) (.branch 57 (.branch 56 (.leaf (-22)) (.leaf (-20))) (.branch 58 (.leaf (-18)) (.leaf (-16))))) (.branch 62 (.branch 60 (.leaf (-14)) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 62 (.branch 60 (.branch 59 (.leaf (-16)) (.leaf (-14))) (.branch 61 (.leaf (-12)) (.leaf (-10)))) (.branch 64 (.branch 63 (.leaf (-8)) (.leaf (-6))) (.branch 65 (.leaf (-4)) (.leaf (-2))))),
  (.branch 48 (.leaf (-5)) (.branch 65 (.leaf (-4)) (.leaf (-2)))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_142_1197 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (4)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (6)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (4))) (.branch 40 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (3))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (1))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (2))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (3)) (.leaf (0))) (.branch 60 (.leaf (1)) (.leaf (4)))) (.branch 63 (.branch 62 (.leaf (2)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (3)) (.leaf (2)))))))))
  code := certificateD8_1197
  counts := ![(.branch 30 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))) (.branch 48 (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 59 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))) (.branch 51 (.branch 42 (.branch 38 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 60 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.leaf (15)))))),
  (.branch 35 (.branch 18 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 44 (.branch 40 (.leaf (8)) (.leaf (9))) (.branch 49 (.leaf (10)) (.leaf (11)))) (.branch 62 (.branch 57 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.leaf (15)))))),
  (.branch 32 (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 36 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 54 (.leaf (9)) (.leaf (10))) (.branch 65 (.leaf (11)) (.leaf (12)))))),
  (.branch 39 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 61 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))) (.branch 47 (.branch 36 (.leaf (-5)) (.leaf (-6))) (.branch 58 (.leaf (-7)) (.leaf (-8))))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-60))),
  (.branch 28 (.leaf (0)) (.leaf (-38))),
  (.branch 50 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 64 (.branch 60 (.leaf (-10)) (.leaf (-9))) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 56 (.branch 47 (.leaf (-12)) (.leaf (-11))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 58 (.leaf (-1)) (.leaf (0))),
  (.branch 59 (.leaf (-8)) (.leaf (-7))),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-60)) (.branch 8 (.leaf (-59)) (.leaf (-58)))) (.branch 11 (.branch 10 (.leaf (-57)) (.leaf (-56))) (.branch 12 (.leaf (-55)) (.leaf (-54))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-53)) (.leaf (-52))) (.branch 16 (.leaf (-51)) (.leaf (-50)))) (.branch 19 (.branch 18 (.leaf (-49)) (.leaf (-48))) (.branch 20 (.leaf (-47)) (.leaf (-46)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-45)) (.branch 23 (.leaf (-44)) (.leaf (-43)))) (.branch 26 (.branch 25 (.leaf (-42)) (.leaf (-41))) (.branch 27 (.leaf (-40)) (.leaf (-39))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-38)) (.leaf (-37))) (.branch 31 (.leaf (-36)) (.leaf (-35)))) (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.leaf (-31))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 41 (.branch 40 (.leaf (-27)) (.leaf (-26))) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))))) (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 37 (.branch 32 (.branch 30 (.branch 29 (.leaf (-38)) (.leaf (-37))) (.branch 31 (.leaf (-36)) (.leaf (-35)))) (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.branch 36 (.leaf (-31)) (.leaf (-30)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (-29)) (.leaf (-28))) (.branch 40 (.leaf (-27)) (.branch 41 (.leaf (-26)) (.leaf (-25))))) (.branch 44 (.branch 43 (.leaf (-24)) (.leaf (-23))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))))) (.branch 56 (.branch 51 (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))))) (.branch 61 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6))))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 54 (.branch 52 (.branch 51 (.leaf (-16)) (.leaf (-15))) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_142_1198 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (7)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (2))) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (3)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (7)) (.leaf (1))) (.branch 40 (.leaf (0)) (.leaf (5))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (4)) (.leaf (2))) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (6)) (.leaf (4)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (5)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (1))) (.branch 56 (.leaf (4)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (7))) (.branch 60 (.leaf (0)) (.leaf (1)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (5))) (.branch 64 (.leaf (0)) (.branch 65 (.leaf (2)) (.leaf (4)))))))))
  code := certificateD8_1198
  counts := ![(.branch 31 (.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 17 (.leaf (5)) (.leaf (6))) (.branch 24 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))))) (.branch 46 (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 40 (.leaf (12)) (.branch 44 (.leaf (13)) (.leaf (14))))) (.branch 57 (.branch 50 (.leaf (15)) (.branch 53 (.leaf (16)) (.leaf (17)))) (.branch 60 (.leaf (18)) (.branch 64 (.leaf (19)) (.leaf (20))))))),
  (.branch 32 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 55 (.leaf (7)) (.branch 61 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 51 (.branch 43 (.leaf (5)) (.leaf (6))) (.branch 58 (.leaf (7)) (.branch 65 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 54 (.leaf (6)) (.branch 62 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))) (.branch 49 (.branch 42 (.leaf (4)) (.leaf (5))) (.branch 56 (.leaf (6)) (.branch 66 (.leaf (7)) (.leaf (8)))))),
  (.branch 30 (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 52 (.branch 41 (.leaf (3)) (.leaf (4))) (.branch 63 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 38 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 59 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))) (.branch 40 (.branch 13 (.leaf (-16)) (.leaf (-20))) (.branch 46 (.leaf (-21)) (.leaf (-25))))),
  (.branch 39 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 61 (.leaf (-12)) (.leaf (-13)))),
  (.branch 28 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 36 (.leaf (-11)) (.leaf (-13)))),
  (.branch 23 (.branch 16 (.leaf (0)) (.leaf (-2))) (.branch 49 (.leaf (-4)) (.branch 56 (.leaf (-5)) (.leaf (-7))))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18)))),
  (.branch 15 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 54 (.branch 47 (.leaf (-25)) (.leaf (-24))) (.branch 61 (.leaf (-23)) (.branch 65 (.leaf (-20)) (.leaf (-15))))),
  (.branch 63 (.branch 62 (.leaf (-13)) (.leaf (-11))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 63 (.branch 37 (.leaf (-13)) (.leaf (-12))) (.branch 64 (.leaf (-10)) (.branch 65 (.leaf (-8)) (.leaf (-6))))),
  (.branch 60 (.branch 58 (.branch 57 (.leaf (-7)) (.leaf (-6))) (.branch 59 (.leaf (-5)) (.leaf (-4)))) (.branch 62 (.branch 61 (.leaf (-3)) (.leaf (-2))) (.branch 63 (.leaf (-1)) (.leaf (0))))),
  (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))),
  (.branch 57 (.branch 52 (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-17))) (.branch 51 (.leaf (-16)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-14)) (.leaf (-13))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-11)) (.leaf (-10)))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (-9)) (.leaf (-8))) (.branch 60 (.leaf (-7)) (.leaf (-6)))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 62 (.branch 60 (.leaf (-7)) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_142_1199 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (1)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (2)) (.leaf (1)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (1)) (.leaf (4))) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (2)) (.leaf (0)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (7))) (.branch 52 (.leaf (0)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (3)) (.leaf (1))) (.branch 56 (.leaf (0)) (.leaf (4))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (2)) (.leaf (1))) (.branch 60 (.leaf (0)) (.leaf (2)))) (.branch 63 (.branch 62 (.leaf (3)) (.leaf (0))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (4)) (.leaf (2)))))))))
  code := certificateD8_1199
  counts := ![(.branch 30 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))) (.branch 49 (.branch 38 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.branch 45 (.leaf (12)) (.leaf (13))))) (.branch 56 (.branch 52 (.leaf (14)) (.leaf (15))) (.branch 60 (.leaf (16)) (.branch 63 (.leaf (17)) (.leaf (18))))))),
  (.branch 33 (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))) (.branch 50 (.branch 42 (.branch 37 (.leaf (8)) (.leaf (9))) (.branch 46 (.leaf (10)) (.leaf (11)))) (.branch 59 (.branch 55 (.leaf (12)) (.leaf (13))) (.branch 64 (.leaf (14)) (.leaf (15)))))),
  (.branch 36 (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))) (.branch 53 (.branch 44 (.branch 39 (.leaf (8)) (.leaf (9))) (.branch 48 (.leaf (10)) (.leaf (11)))) (.branch 61 (.branch 58 (.leaf (12)) (.leaf (13))) (.branch 66 (.leaf (14)) (.leaf (15)))))),
  (.branch 32 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 47 (.branch 40 (.leaf (5)) (.leaf (6))) (.branch 54 (.leaf (7)) (.branch 62 (.leaf (8)) (.leaf (9)))))),
  (.branch 35 (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 57 (.branch 43 (.leaf (3)) (.leaf (4))) (.branch 65 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 51 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 39 (.leaf (-2)) (.branch 61 (.leaf (-3)) (.leaf (-4))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 43 (.branch 21 (.leaf (0)) (.leaf (-5))) (.branch 65 (.leaf (-9)) (.leaf (-13)))),
  (.branch 7 (.leaf (0)) (.leaf (-59))),
  (.branch 29 (.leaf (0)) (.leaf (-37))),
  (.branch 51 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3)))),
  (.branch 60 (.branch 51 (.leaf (-14)) (.leaf (-13))) (.branch 65 (.leaf (-10)) (.leaf (-5)))),
  (.branch 62 (.leaf (-4)) (.branch 63 (.leaf (-2)) (.leaf (0)))),
  (.branch 63 (.branch 55 (.leaf (-14)) (.leaf (-12))) (.branch 64 (.leaf (-9)) (.branch 65 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-13)),
  (.branch 36 (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-59)) (.branch 9 (.leaf (-58)) (.leaf (-57)))) (.branch 12 (.branch 11 (.leaf (-56)) (.leaf (-55))) (.branch 13 (.leaf (-54)) (.leaf (-53))))) (.branch 17 (.branch 15 (.leaf (-52)) (.branch 16 (.leaf (-51)) (.leaf (-50)))) (.branch 19 (.branch 18 (.leaf (-49)) (.leaf (-48))) (.branch 20 (.leaf (-47)) (.leaf (-46)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-45)) (.branch 23 (.leaf (-44)) (.leaf (-43)))) (.branch 26 (.branch 25 (.leaf (-42)) (.leaf (-41))) (.branch 27 (.leaf (-40)) (.leaf (-39))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-38)) (.leaf (-37))) (.branch 31 (.leaf (-36)) (.leaf (-35)))) (.branch 34 (.branch 33 (.leaf (-34)) (.leaf (-33))) (.branch 35 (.leaf (-32)) (.leaf (-31))))))) (.branch 51 (.branch 43 (.branch 39 (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-29)) (.leaf (-28)))) (.branch 41 (.branch 40 (.leaf (-27)) (.leaf (-26))) (.branch 42 (.leaf (-25)) (.leaf (-24))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.leaf (-20)))) (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))))) (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-37)) (.leaf (-36))) (.branch 32 (.leaf (-35)) (.leaf (-34)))) (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-32))) (.branch 36 (.leaf (-31)) (.branch 37 (.leaf (-30)) (.leaf (-29)))))) (.branch 42 (.branch 40 (.branch 39 (.leaf (-28)) (.leaf (-27))) (.branch 41 (.leaf (-26)) (.leaf (-25)))) (.branch 44 (.branch 43 (.leaf (-24)) (.leaf (-23))) (.branch 45 (.leaf (-22)) (.branch 46 (.leaf (-21)) (.leaf (-20))))))) (.branch 56 (.branch 51 (.branch 49 (.branch 48 (.leaf (-19)) (.leaf (-18))) (.branch 50 (.leaf (-17)) (.leaf (-16)))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-14))) (.branch 54 (.leaf (-13)) (.branch 55 (.leaf (-12)) (.leaf (-11)))))) (.branch 61 (.branch 58 (.branch 57 (.leaf (-10)) (.leaf (-9))) (.branch 59 (.leaf (-8)) (.branch 60 (.leaf (-7)) (.leaf (-6))))) (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 58 (.branch 54 (.branch 52 (.leaf (-15)) (.branch 53 (.leaf (-14)) (.leaf (-13)))) (.branch 56 (.branch 55 (.leaf (-12)) (.leaf (-11))) (.branch 57 (.leaf (-10)) (.leaf (-9))))) (.branch 62 (.branch 60 (.branch 59 (.leaf (-8)) (.leaf (-7))) (.branch 61 (.leaf (-6)) (.leaf (-5)))) (.branch 64 (.branch 63 (.leaf (-4)) (.leaf (-3))) (.branch 65 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_142_1200 : CycleWitness 8 where
  length := 66
  word := (.branch 33 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (6)) (.leaf (4))) (.branch 23 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (7))) (.branch 27 (.leaf (3)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (4)))))))) (.branch 49 (.branch 41 (.branch 37 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 40 (.leaf (7)) (.leaf (1))))) (.branch 45 (.branch 43 (.branch 42 (.leaf (2)) (.leaf (0))) (.branch 44 (.leaf (4)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (6)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2)))))) (.branch 57 (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (3))) (.branch 52 (.leaf (0)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (7)) (.leaf (4))) (.branch 56 (.leaf (2)) (.leaf (0))))) (.branch 61 (.branch 59 (.branch 58 (.leaf (1)) (.leaf (6))) (.branch 60 (.leaf (3)) (.leaf (5)))) (.branch 63 (.branch 62 (.leaf (0)) (.leaf (2))) (.branch 64 (.leaf (1)) (.branch 65 (.leaf (7)) (.leaf (4)))))))))
  code := certificateD8_1200
  counts := ![(.branch 29 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))) (.branch 48 (.branch 38 (.branch 34 (.leaf (7)) (.leaf (8))) (.branch 43 (.leaf (9)) (.leaf (10)))) (.branch 57 (.branch 52 (.leaf (11)) (.leaf (12))) (.branch 62 (.leaf (13)) (.leaf (14)))))),
  (.branch 31 (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))) (.branch 47 (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))) (.branch 58 (.branch 53 (.leaf (9)) (.leaf (10))) (.branch 64 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 49 (.branch 37 (.leaf (5)) (.branch 42 (.leaf (6)) (.leaf (7)))) (.branch 56 (.leaf (8)) (.branch 63 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 45 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 60 (.leaf (7)) (.leaf (8)))))),
  (.branch 33 (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 44 (.leaf (3)) (.leaf (4))) (.branch 66 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 39 (.leaf (3)) (.leaf (4))) (.branch 61 (.leaf (5)) (.leaf (6))))),
  (.branch 32 (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (3)) (.branch 59 (.leaf (4)) (.leaf (5))))),
  (.branch 40 (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 54 (.leaf (3)) (.branch 65 (.leaf (4)) (.leaf (5)))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-26))) (.branch 19 (.leaf (-31)) (.leaf (-32)))),
  (.branch 2 (.leaf (0)) (.branch 35 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 42 (.leaf (-18)) (.leaf (-21)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 51 (.leaf (-24)) (.leaf (-29)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-13)) (.leaf (-17)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 65 (.leaf (-2)) (.leaf (-5))))]
  high := ![(.branch 63 (.branch 53 (.leaf (-32)) (.branch 58 (.leaf (-30)) (.leaf (-28)))) (.branch 64 (.leaf (-21)) (.branch 65 (.leaf (-14)) (.leaf (-7))))),
  (.branch 59 (.branch 36 (.leaf (-14)) (.leaf (-13))) (.branch 65 (.leaf (-12)) (.leaf (-9)))),
  (.branch 57 (.branch 43 (.leaf (-21)) (.branch 50 (.leaf (-20)) (.leaf (-19)))) (.branch 64 (.leaf (-18)) (.branch 65 (.leaf (-14)) (.leaf (-10))))),
  (.branch 62 (.branch 52 (.leaf (-29)) (.branch 61 (.leaf (-28)) (.leaf (-25)))) (.branch 64 (.branch 63 (.leaf (-22)) (.leaf (-19))) (.branch 65 (.leaf (-16)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 63 (.branch 62 (.leaf (-5)) (.leaf (-4))) (.branch 64 (.leaf (-3)) (.branch 65 (.leaf (-2)) (.leaf (-1))))),
  (.branch 62 (.branch 60 (.leaf (-17)) (.branch 61 (.leaf (-15)) (.leaf (-13)))) (.branch 64 (.branch 63 (.leaf (-11)) (.leaf (-9))) (.branch 65 (.leaf (-7)) (.leaf (-5))))),
  (.leaf (-5))]
def witnessD8_142 : Fin 15 → CycleWitness 8 := ![witnessD8_142_1186, witnessD8_142_1187, witnessD8_142_1188, witnessD8_142_1189, witnessD8_142_1190, witnessD8_142_1191, witnessD8_142_1192, witnessD8_142_1193, witnessD8_142_1194, witnessD8_142_1195, witnessD8_142_1196, witnessD8_142_1197, witnessD8_142_1198, witnessD8_142_1199, witnessD8_142_1200]
end RealPinwheel.FiveSixths


