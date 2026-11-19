-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_178
-- name    : RealPinwheel_FiveSixths_WitnessD8_178
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:29:08.477653+00:00
-- url     : https://prove2.me/theorems/5948b47d-5de6-4d8e-b9ff-dd013aeea3d3
-- title:
--   Exact witness block D8_178
-- statement:
--   These exact witnesses represent words 1779 through 1797 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1779–1797; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_178_1778 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (7)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (0))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (4)) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (7))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (3)) (.branch 41 (.leaf (6)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (4)) (.branch 47 (.leaf (5)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (7))) (.branch 51 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1778
  counts := ![(.branch 23 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 30 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 39 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 37 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 44 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 29 (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 51 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 38 (.leaf (3)) (.branch 46 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 23 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 13 (.leaf (-8)) (.leaf (-9)))) (.branch 35 (.branch 26 (.leaf (-10)) (.leaf (-11))) (.branch 45 (.leaf (-14)) (.leaf (-15))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-34))) (.branch 42 (.leaf (-37)) (.leaf (-38)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 46 (.leaf (-7)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-34))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 50 (.branch 46 (.leaf (-15)) (.leaf (-14))) (.branch 51 (.leaf (-12)) (.leaf (-10)))),
  (.branch 49 (.branch 43 (.leaf (-38)) (.leaf (-36))) (.branch 50 (.leaf (-27)) (.branch 51 (.leaf (-18)) (.leaf (-9))))),
  (.branch 37 (.branch 21 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 46 (.branch 45 (.leaf (-14)) (.leaf (-9))) (.branch 47 (.leaf (-4)) (.leaf (0))))),
  (.branch 30 (.branch 19 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.leaf (-11)))),
  (.branch 49 (.branch 47 (.leaf (-9)) (.branch 48 (.leaf (-8)) (.leaf (-7)))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 7 (.leaf (-34)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_178_1779 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (5)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (6)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (5)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1779
  counts := ![(.branch 25 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 29 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.branch 49 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 46 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7)))),
  (.branch 42 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_178_1780 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (3))) (.branch 38 (.leaf (0)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (4)) (.leaf (0)))) (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (5)) (.leaf (3))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1780
  counts := ![(.branch 25 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 20 (.leaf (9)) (.branch 22 (.leaf (10)) (.leaf (11)))))) (.branch 38 (.branch 31 (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14)))) (.branch 33 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20)))) (.branch 48 (.branch 46 (.leaf (21)) (.leaf (22))) (.branch 51 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 7 (.leaf (-9)) (.branch 9 (.leaf (-10)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-34)) (.leaf (-35)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (-7))) (.branch 49 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-40)) (.leaf (-41)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (-13))) (.branch 47 (.leaf (-14)) (.leaf (-15))))]
  high := ![(.branch 49 (.leaf (-11)) (.leaf (-6))),
  (.branch 48 (.branch 46 (.branch 37 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 43 (.branch 24 (.leaf (-35)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 45 (.branch 41 (.branch 22 (.leaf (-41)) (.branch 40 (.leaf (-39)) (.leaf (-36)))) (.branch 43 (.branch 42 (.leaf (-33)) (.leaf (-30))) (.branch 44 (.leaf (-27)) (.leaf (-24))))) (.branch 48 (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-18)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))]
def witnessD8_178_1781 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3)))) (.branch 43 (.leaf (5)) (.branch 44 (.leaf (0)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (0))) (.branch 51 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_1781
  counts := ![(.branch 24 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))) (.branch 38 (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (13))))) (.branch 44 (.branch 41 (.leaf (14)) (.leaf (15))) (.branch 47 (.leaf (16)) (.branch 50 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 31 (.leaf (-19)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (-3))) (.branch 48 (.leaf (-6)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-48))),
  (.branch 30 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 39 (.branch 33 (.branch 30 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.leaf (-22)))) (.branch 45 (.branch 42 (.leaf (-21)) (.leaf (-20))) (.branch 48 (.leaf (-19)) (.branch 51 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 41 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 50 (.leaf (-19)) (.branch 51 (.leaf (-14)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 16 (.branch 10 (.branch 7 (.branch 5 (.leaf (-48)) (.branch 6 (.leaf (-47)) (.leaf (-46)))) (.branch 8 (.leaf (-45)) (.branch 9 (.leaf (-44)) (.leaf (-43))))) (.branch 13 (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40)))) (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31))))) (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25))))))) (.branch 40 (.branch 34 (.branch 31 (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19))))) (.branch 37 (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))))) (.branch 46 (.branch 43 (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_178_1782 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (6)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1782
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-43))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 35 (.leaf (0)) (.leaf (-17))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 47 (.leaf (-11)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.leaf (-7)) (.leaf (-4))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 46 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-43)) (.leaf (-42))) (.branch 12 (.leaf (-41)) (.branch 13 (.leaf (-40)) (.leaf (-39))))) (.branch 16 (.branch 15 (.leaf (-38)) (.leaf (-37))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_178_1783 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (7)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1783
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 35 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))) (.branch 23 (.leaf (-20)) (.branch 49 (.leaf (-23)) (.leaf (-25))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 8 (.leaf (-13)) (.branch 34 (.leaf (-17)) (.leaf (-20))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 41 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-25)) (.leaf (-26)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 50 (.leaf (-25)) (.branch 51 (.leaf (-18)) (.leaf (-11)))),
  (.branch 43 (.branch 35 (.leaf (-20)) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 47 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 49 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 45 (.branch 27 (.leaf (-26)) (.leaf (-24))) (.branch 46 (.leaf (-21)) (.leaf (-18)))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (0)),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_178_1784 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (5)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (7)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1784
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 51 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-30))),
  (.branch 48 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 47 (.leaf (-11)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 48 (.leaf (-7)) (.leaf (-4))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 29 (.branch 25 (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-25)) (.leaf (-24))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_178_1785 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (6)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (3))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_1785
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))) (.branch 37 (.branch 24 (.leaf (-7)) (.leaf (-8))) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-39))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.branch 39 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 51 (.leaf (-10)) (.leaf (-7))),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-39)) (.leaf (-38))) (.branch 16 (.leaf (-37)) (.leaf (-36)))) (.branch 19 (.branch 18 (.leaf (-35)) (.leaf (-34))) (.branch 20 (.leaf (-33)) (.branch 21 (.leaf (-32)) (.leaf (-31)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-30)) (.leaf (-29))) (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))))) (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_178_1786 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (7))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (1)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_1786
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 35 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 38 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 51 (.leaf (11)) (.leaf (12)))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.branch 52 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))) (.branch 37 (.branch 24 (.leaf (-7)) (.leaf (-8))) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 19 (.leaf (0)) (.leaf (-33))),
  (.branch 45 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 51 (.leaf (-10)) (.leaf (-7))),
  (.branch 43 (.leaf (-4)) (.leaf (-3))),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 35 (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.leaf (-30)))) (.branch 25 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.leaf (-18)))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_178_1787 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (5))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (3)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 38 (.leaf (1)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (7))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_1787
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 46 (.branch 42 (.leaf (11)) (.leaf (12))) (.branch 50 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 44 (.branch 35 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))) (.branch 23 (.leaf (-20)) (.branch 49 (.leaf (-23)) (.leaf (-25))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 8 (.leaf (-13)) (.branch 34 (.leaf (-17)) (.leaf (-20))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 41 (.leaf (-15)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-33))),
  (.branch 45 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 50 (.leaf (-25)) (.branch 51 (.leaf (-18)) (.leaf (-11)))),
  (.branch 43 (.branch 35 (.leaf (-20)) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 47 (.leaf (-17)) (.branch 51 (.leaf (-16)) (.leaf (-11))))),
  (.branch 49 (.branch 42 (.leaf (-17)) (.leaf (-16))) (.branch 50 (.leaf (-13)) (.branch 51 (.leaf (-10)) (.leaf (-7))))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 42 (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))) (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.leaf (-30)))) (.branch 25 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 26 (.leaf (-27)) (.leaf (-26))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22)))) (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.leaf (-18)))))) (.branch 43 (.branch 39 (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))) (.branch 41 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-11)) (.leaf (-10))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_178_1788 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (7)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (7))))) (.branch 35 (.branch 33 (.leaf (5)) (.branch 34 (.leaf (0)) (.leaf (1)))) (.branch 37 (.branch 36 (.leaf (3)) (.leaf (0))) (.branch 38 (.leaf (4)) (.leaf (1)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (5))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3)))) (.branch 50 (.branch 49 (.leaf (7)) (.leaf (0))) (.branch 51 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1788
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 50 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 39 (.branch 31 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 35 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 49 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 20 (.leaf (-18)) (.branch 46 (.leaf (-21)) (.leaf (-23))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 31 (.leaf (-13)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-34)) (.leaf (-35)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (-7))) (.branch 49 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 47 (.leaf (-23)) (.branch 51 (.leaf (-18)) (.leaf (-11)))),
  (.branch 40 (.branch 32 (.leaf (-16)) (.branch 36 (.leaf (-15)) (.leaf (-14)))) (.branch 44 (.leaf (-13)) (.branch 48 (.leaf (-12)) (.leaf (-11))))),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-10)) (.leaf (-9))) (.branch 45 (.leaf (-8)) (.branch 46 (.leaf (-7)) (.leaf (-6))))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 43 (.branch 24 (.leaf (-35)) (.branch 42 (.leaf (-33)) (.leaf (-30)))) (.branch 44 (.leaf (-27)) (.branch 45 (.leaf (-24)) (.leaf (-21))))) (.branch 49 (.branch 47 (.leaf (-18)) (.branch 48 (.leaf (-15)) (.leaf (-12)))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3))))]
def witnessD8_178_1789 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (5)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (6)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1789
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-42))),
  (.branch 36 (.leaf (0)) (.leaf (-16))),
  (.branch 49 (.leaf (0)) (.leaf (-3))),
  (.branch 23 (.leaf (0)) (.leaf (-29)))]
  high := ![(.branch 46 (.leaf (-9)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 42 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-42)) (.leaf (-41))) (.branch 13 (.leaf (-40)) (.branch 14 (.leaf (-39)) (.leaf (-38))))) (.branch 17 (.branch 16 (.leaf (-37)) (.leaf (-36))) (.branch 18 (.leaf (-35)) (.branch 19 (.leaf (-34)) (.leaf (-33)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-32)) (.leaf (-31))) (.branch 23 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28))))) (.branch 28 (.branch 26 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 29 (.leaf (-24)) (.branch 30 (.leaf (-23)) (.leaf (-22))))))) (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 30 (.branch 26 (.branch 24 (.leaf (-29)) (.branch 25 (.leaf (-28)) (.leaf (-27)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 29 (.leaf (-24)) (.leaf (-23))))) (.branch 33 (.branch 31 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))))) (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_178_1790 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 33 (.leaf (1)) (.branch 34 (.leaf (6)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (2)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (3)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (1)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (2)) (.leaf (1))) (.branch 51 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1790
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 32 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 49 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.branch 44 (.leaf (-4)) (.leaf (-5))))),
  (.branch 8 (.leaf (0)) (.leaf (-44))),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 34 (.leaf (0)) (.leaf (-18))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 46 (.leaf (-9)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 42 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 43 (.leaf (-7)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 47 (.branch 45 (.leaf (-5)) (.branch 46 (.leaf (-4)) (.leaf (-3)))) (.branch 48 (.leaf (-2)) (.branch 49 (.leaf (-1)) (.leaf (0))))),
  (.branch 30 (.branch 19 (.branch 13 (.branch 10 (.branch 9 (.leaf (-44)) (.leaf (-43))) (.branch 11 (.leaf (-42)) (.branch 12 (.leaf (-41)) (.leaf (-40))))) (.branch 16 (.branch 14 (.leaf (-39)) (.branch 15 (.leaf (-38)) (.leaf (-37)))) (.branch 17 (.leaf (-36)) (.branch 18 (.leaf (-35)) (.leaf (-34)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-33)) (.leaf (-32))) (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29))))) (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 28 (.leaf (-25)) (.branch 29 (.leaf (-24)) (.leaf (-23))))))) (.branch 41 (.branch 35 (.branch 32 (.branch 31 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18))))) (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_178_1791 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (0)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (5))) (.branch 38 (.leaf (0)) (.leaf (2)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (7))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1791
  counts := ![(.branch 25 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (10)) (.leaf (11))) (.branch 33 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14))))) (.branch 46 (.branch 40 (.leaf (15)) (.branch 43 (.leaf (16)) (.leaf (17)))) (.branch 48 (.leaf (18)) (.branch 51 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 47 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 52 (.leaf (11)) (.leaf (12)))))),
  (.branch 5 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 50 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.branch 42 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-28))),
  (.branch 50 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 41 (.leaf (-8)) (.branch 49 (.leaf (-7)) (.leaf (-5)))),
  (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 41 (.branch 36 (.branch 33 (.branch 32 (.leaf (-21)) (.leaf (-20))) (.branch 34 (.leaf (-19)) (.branch 35 (.leaf (-18)) (.leaf (-17))))) (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))))) (.branch 46 (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-8)) (.leaf (-7))))) (.branch 49 (.branch 47 (.leaf (-6)) (.branch 48 (.leaf (-5)) (.leaf (-4)))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 40 (.branch 38 (.leaf (-15)) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 31 (.branch 27 (.branch 25 (.leaf (-28)) (.branch 26 (.leaf (-27)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-25)) (.leaf (-24))) (.branch 30 (.leaf (-23)) (.leaf (-22))))) (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-20)) (.leaf (-19)))) (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))))) (.branch 45 (.branch 41 (.branch 39 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-12)))) (.branch 43 (.branch 42 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_178_1792 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (4))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (3)) (.leaf (4)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (7)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1792
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_178_1793 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (6)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (2))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (4)) (.leaf (0)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (2)) (.branch 41 (.leaf (1)) (.leaf (0)))) (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (7)) (.leaf (0)))) (.branch 50 (.branch 49 (.leaf (1)) (.leaf (4))) (.branch 51 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1793
  counts := ![(.branch 25 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 39 (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.branch 36 (.leaf (12)) (.leaf (13))))) (.branch 45 (.branch 42 (.leaf (14)) (.leaf (15))) (.branch 48 (.leaf (16)) (.branch 51 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 49 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 29 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 52 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-6)) (.branch 44 (.leaf (-9)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-31))),
  (.branch 47 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 37 (.branch 31 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 43 (.branch 40 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.branch 49 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 50 (.branch 45 (.leaf (-11)) (.leaf (-10))) (.branch 51 (.leaf (-8)) (.leaf (-6)))),
  (.branch 48 (.branch 41 (.leaf (-8)) (.branch 47 (.leaf (-7)) (.leaf (-5)))) (.branch 49 (.leaf (-3)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 51 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.branch 38 (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-16)) (.leaf (-15)))) (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-11)) (.leaf (-10)))))) (.branch 47 (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.leaf (-6)))) (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 28 (.branch 24 (.branch 22 (.leaf (-31)) (.branch 23 (.leaf (-30)) (.leaf (-29)))) (.branch 26 (.branch 25 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-24)) (.leaf (-23))) (.branch 31 (.leaf (-22)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-17)))))) (.branch 44 (.branch 40 (.branch 38 (.branch 37 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-13)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9))))) (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 48 (.leaf (-5)) (.leaf (-4))) (.branch 50 (.leaf (-3)) (.branch 51 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_178_1794 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (6)) (.leaf (5))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (7)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (6)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (7)) (.leaf (5))))))))
  code := certificateD8_1794
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 41 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 34 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 25 (.branch 8 (.leaf (0)) (.leaf (-28))) (.branch 42 (.leaf (-29)) (.leaf (-30)))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 46 (.leaf (-8)) (.branch 51 (.leaf (-6)) (.leaf (-3)))),
  (.branch 48 (.branch 30 (.leaf (-17)) (.branch 39 (.leaf (-16)) (.leaf (-15)))) (.branch 50 (.branch 49 (.leaf (-12)) (.leaf (-9))) (.branch 51 (.leaf (-6)) (.leaf (-3))))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 47 (.branch 44 (.branch 43 (.leaf (-30)) (.leaf (-27))) (.branch 45 (.leaf (-24)) (.branch 46 (.leaf (-21)) (.leaf (-18))))) (.branch 49 (.branch 48 (.leaf (-15)) (.leaf (-12))) (.branch 50 (.leaf (-9)) (.branch 51 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3)))]
def witnessD8_178_1795 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (1))))) (.branch 35 (.branch 33 (.leaf (2)) (.branch 34 (.leaf (0)) (.leaf (4)))) (.branch 37 (.branch 36 (.leaf (1)) (.leaf (2))) (.branch 38 (.leaf (0)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2)))) (.branch 43 (.leaf (1)) (.branch 44 (.leaf (3)) (.leaf (0))))) (.branch 48 (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (4)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (2))) (.branch 51 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_1795
  counts := ![(.branch 23 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 38 (.branch 30 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 45 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 49 (.leaf (13)) (.leaf (14)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 32 (.branch 28 (.leaf (7)) (.leaf (8))) (.branch 36 (.leaf (9)) (.leaf (10)))) (.branch 47 (.branch 43 (.leaf (11)) (.leaf (12))) (.branch 51 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 37 (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 46 (.branch 42 (.leaf (9)) (.leaf (10))) (.branch 50 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 46 (.branch 42 (.leaf (-25)) (.leaf (-23))) (.branch 50 (.leaf (-21)) (.branch 51 (.leaf (-14)) (.leaf (-7))))),
  (.branch 44 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-9)) (.leaf (-7)))),
  (.branch 51 (.leaf (-6)) (.leaf (-3))),
  (.branch 48 (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))),
  (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_178_1796 : CycleWitness 8 where
  length := 52
  word := (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (3)) (.leaf (6))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 36 (.leaf (0)) (.leaf (4))) (.branch 38 (.leaf (3)) (.leaf (5)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))) (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (4))))) (.branch 48 (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 49 (.leaf (0)) (.leaf (4))) (.branch 51 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_1796
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.branch 49 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 25 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 24 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (-1)) (.leaf (-3)))) (.branch 37 (.leaf (-4)) (.branch 50 (.leaf (-5)) (.leaf (-6))))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 26 (.leaf (0)) (.leaf (-26))),
  (.leaf (0))]
  high := ![(.branch 50 (.leaf (-12)) (.branch 51 (.leaf (-8)) (.leaf (-4)))),
  (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-8))) (.branch 50 (.leaf (-6)) (.branch 51 (.leaf (-4)) (.leaf (-2))))),
  (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-6))) (.branch 51 (.leaf (-4)) (.leaf (-2)))),
  (.branch 45 (.leaf (-3)) (.leaf (-2))),
  (.branch 51 (.leaf (-6)) (.leaf (-5))),
  (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (-26)) (.branch 28 (.leaf (-25)) (.leaf (-24)))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-20)) (.branch 34 (.leaf (-19)) (.leaf (-18)))) (.branch 37 (.branch 36 (.leaf (-17)) (.leaf (-16))) (.branch 38 (.leaf (-15)) (.leaf (-14)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 43 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8))))) (.branch 48 (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5)))) (.branch 50 (.branch 49 (.leaf (-4)) (.leaf (-3))) (.branch 51 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_178 : Fin 19 → CycleWitness 8 := ![witnessD8_178_1778, witnessD8_178_1779, witnessD8_178_1780, witnessD8_178_1781, witnessD8_178_1782, witnessD8_178_1783, witnessD8_178_1784, witnessD8_178_1785, witnessD8_178_1786, witnessD8_178_1787, witnessD8_178_1788, witnessD8_178_1789, witnessD8_178_1790, witnessD8_178_1791, witnessD8_178_1792, witnessD8_178_1793, witnessD8_178_1794, witnessD8_178_1795, witnessD8_178_1796]
end RealPinwheel.FiveSixths


