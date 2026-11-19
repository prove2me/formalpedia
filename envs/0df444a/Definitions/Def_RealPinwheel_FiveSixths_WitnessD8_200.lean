-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_200
-- name    : RealPinwheel_FiveSixths_WitnessD8_200
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:43:18.159312+00:00
-- url     : https://prove2.me/theorems/29880073-b9fc-47d0-95b2-44ed78bbf806
-- title:
--   Exact witness block D8_200
-- statement:
--   These exact witnesses represent words 2229 through 2251 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2229–2251; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_200_2228 : CycleWitness 8 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (7)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (7)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (1))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (6))))) (.branch 29 (.branch 27 (.leaf (5)) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (4)) (.leaf (3)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (1)) (.leaf (7))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (2)) (.leaf (5))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (0)) (.leaf (3)))) (.branch 41 (.leaf (6)) (.branch 42 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2228
  counts := ![(.branch 17 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 22 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 25 (.leaf (-12)) (.leaf (-13)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 33 (.leaf (-11)) (.branch 38 (.leaf (-12)) (.leaf (-15))))),
  (.branch 19 (.branch 13 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-3)) (.branch 29 (.leaf (-8)) (.leaf (-13))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (-13))) (.branch 40 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 37 (.leaf (-23)) (.leaf (-24)))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 40 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-8)) (.leaf (-6))))),
  (.branch 40 (.branch 39 (.leaf (-15)) (.leaf (-13))) (.branch 41 (.leaf (-11)) (.branch 42 (.leaf (-9)) (.leaf (-7))))),
  (.branch 38 (.branch 30 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-9)))) (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-3)) (.leaf (0))))),
  (.branch 41 (.leaf (-15)) (.branch 42 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))),
  (.branch 40 (.branch 38 (.leaf (-24)) (.branch 39 (.leaf (-20)) (.leaf (-16)))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.branch 12 (.leaf (-7)) (.leaf (-6))) (.branch 42 (.leaf (-5)) (.leaf (-3)))),
  (.branch 38 (.branch 35 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 39 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.branch 42 (.leaf (-4)) (.leaf (-3))))))]
def witnessD8_200_2229 : CycleWitness 8 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (3))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (7)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (1)) (.leaf (4))))) (.branch 29 (.branch 27 (.leaf (6)) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (2)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (5)) (.leaf (1))) (.branch 35 (.leaf (7)) (.branch 36 (.leaf (0)) (.leaf (4))))) (.branch 40 (.branch 38 (.leaf (3)) (.branch 39 (.leaf (2)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (6)) (.leaf (5))))))))
  code := certificateD8_2229
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 34 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-17)) (.leaf (-22)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-23))) (.branch 29 (.leaf (-26)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (-23)) (.leaf (-25)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-15)) (.leaf (-18))))]
  high := ![(.branch 37 (.leaf (-9)) (.branch 42 (.leaf (-8)) (.leaf (-6)))),
  (.branch 41 (.branch 35 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 10 (.leaf (-22)) (.branch 32 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.leaf (-14)) (.branch 42 (.leaf (-10)) (.leaf (-6))))),
  (.branch 40 (.branch 30 (.leaf (-27)) (.branch 39 (.leaf (-25)) (.leaf (-20)))) (.branch 41 (.leaf (-15)) (.branch 42 (.leaf (-10)) (.leaf (-5))))),
  (.branch 39 (.branch 27 (.leaf (-25)) (.branch 38 (.leaf (-24)) (.leaf (-20)))) (.branch 41 (.branch 40 (.leaf (-16)) (.leaf (-12))) (.branch 42 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 28 (.leaf (-5)) (.leaf (-3))),
  (.branch 38 (.branch 36 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 37 (.leaf (-15)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-11)) (.leaf (-9))) (.branch 41 (.leaf (-7)) (.branch 42 (.leaf (-5)) (.leaf (-3))))))]
def witnessD8_200_2230 : CycleWitness 8 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (1))))) (.branch 29 (.branch 27 (.leaf (4)) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (6)) (.leaf (1))) (.branch 35 (.leaf (5)) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (4)) (.leaf (0)))) (.branch 41 (.leaf (3)) (.branch 42 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2230
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 36 (.leaf (9)) (.branch 40 (.leaf (10)) (.leaf (11)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 38 (.leaf (9)) (.branch 42 (.leaf (10)) (.leaf (11)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-32)) (.leaf (-39)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-17)) (.leaf (-19)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.leaf (0))]
  high := ![(.branch 29 (.branch 21 (.branch 17 (.leaf (-39)) (.leaf (-38))) (.branch 25 (.leaf (-37)) (.leaf (-36)))) (.branch 37 (.branch 33 (.leaf (-35)) (.leaf (-34))) (.branch 41 (.leaf (-33)) (.branch 42 (.leaf (-22)) (.leaf (-11)))))),
  (.leaf (-2)),
  (.branch 40 (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-16)) (.leaf (-13)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-7)) (.leaf (-4))))),
  (.branch 20 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 42 (.leaf (-8)) (.leaf (-4))))),
  (.branch 40 (.branch 28 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.branch 42 (.leaf (-3)) (.leaf (-2))))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.leaf (-2))))),
  (.branch 37 (.branch 34 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-16)) (.leaf (-14))))) (.branch 40 (.branch 38 (.leaf (-12)) (.branch 39 (.leaf (-10)) (.leaf (-8)))) (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessD8_200_2231 : CycleWitness 8 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (6)) (.leaf (0)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (7)) (.leaf (1))))) (.branch 29 (.branch 27 (.leaf (0)) (.branch 28 (.leaf (5)) (.leaf (4)))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (6)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (3)) (.leaf (0))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (1)) (.leaf (0))))) (.branch 40 (.branch 38 (.leaf (4)) (.branch 39 (.leaf (7)) (.leaf (1)))) (.branch 41 (.leaf (0)) (.branch 42 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_2231
  counts := ![(.branch 20 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 23 (.leaf (7)) (.branch 27 (.leaf (8)) (.leaf (9)))) (.branch 37 (.branch 34 (.leaf (10)) (.leaf (11))) (.branch 41 (.leaf (12)) (.leaf (13)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 40 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.leaf (-22))) (.branch 20 (.leaf (-24)) (.branch 23 (.leaf (-37)) (.leaf (-41))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-17)) (.leaf (-22)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-31)) (.leaf (-34)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 29 (.branch 7 (.leaf (0)) (.leaf (-9))) (.branch 38 (.leaf (-11)) (.leaf (-16)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (-1))) (.branch 42 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-21)) (.leaf (-24)))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 31 (.branch 24 (.leaf (-41)) (.leaf (-40))) (.branch 38 (.leaf (-39)) (.branch 42 (.leaf (-34)) (.leaf (-25))))),
  (.branch 41 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 42 (.leaf (-15)) (.leaf (-9)))),
  (.branch 38 (.branch 25 (.branch 14 (.leaf (-34)) (.leaf (-33))) (.branch 36 (.leaf (-32)) (.branch 37 (.leaf (-28)) (.leaf (-24))))) (.branch 40 (.branch 39 (.leaf (-20)) (.leaf (-16))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 11 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-14))) (.branch 41 (.leaf (-12)) (.branch 42 (.leaf (-10)) (.leaf (-8))))),
  (.leaf (-3)),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-24)) (.branch 33 (.leaf (-23)) (.leaf (-21)))) (.branch 35 (.leaf (-19)) (.branch 36 (.leaf (-17)) (.leaf (-15))))) (.branch 40 (.branch 38 (.leaf (-13)) (.branch 39 (.leaf (-11)) (.leaf (-9)))) (.branch 41 (.leaf (-7)) (.branch 42 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.leaf (-3))))]
def witnessD8_200_2232 : CycleWitness 8 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.leaf (7)) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (5)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2232
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 36 (.leaf (9)) (.branch 40 (.leaf (10)) (.leaf (11)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 38 (.leaf (9)) (.branch 42 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-32)) (.leaf (-39)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-17)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-37))),
  (.branch 27 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 29 (.branch 21 (.branch 17 (.leaf (-39)) (.leaf (-38))) (.branch 25 (.leaf (-37)) (.leaf (-36)))) (.branch 37 (.branch 33 (.leaf (-35)) (.leaf (-34))) (.branch 41 (.leaf (-33)) (.branch 42 (.leaf (-22)) (.leaf (-11)))))),
  (.leaf (-2)),
  (.branch 36 (.leaf (-7)) (.branch 42 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-16)) (.leaf (-13)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 40 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-37)) (.leaf (-36))) (.branch 9 (.leaf (-35)) (.leaf (-34)))) (.branch 12 (.branch 11 (.leaf (-33)) (.leaf (-32))) (.branch 13 (.leaf (-31)) (.branch 14 (.leaf (-30)) (.leaf (-29)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-28)) (.leaf (-27))) (.branch 18 (.leaf (-26)) (.leaf (-25)))) (.branch 21 (.branch 20 (.leaf (-24)) (.leaf (-23))) (.branch 22 (.leaf (-22)) (.branch 23 (.leaf (-21)) (.leaf (-20))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-19)) (.leaf (-18))) (.branch 27 (.leaf (-17)) (.leaf (-16)))) (.branch 30 (.branch 29 (.leaf (-15)) (.leaf (-14))) (.branch 31 (.leaf (-13)) (.branch 32 (.leaf (-12)) (.leaf (-11)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-10)) (.leaf (-9))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-7)) (.leaf (-6))))) (.branch 40 (.branch 39 (.leaf (-5)) (.leaf (-4))) (.branch 41 (.leaf (-3)) (.branch 42 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 31 (.branch 29 (.branch 28 (.leaf (-16)) (.leaf (-15))) (.branch 30 (.leaf (-14)) (.leaf (-13)))) (.branch 33 (.branch 32 (.leaf (-12)) (.leaf (-11))) (.branch 34 (.leaf (-10)) (.leaf (-9))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-7))) (.branch 38 (.leaf (-6)) (.leaf (-5)))) (.branch 41 (.branch 40 (.leaf (-4)) (.leaf (-3))) (.branch 42 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_200_2233 : CycleWitness 8 where
  length := 43
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (7)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.leaf (6)) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (4)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (3))))) (.branch 40 (.branch 38 (.leaf (1)) (.branch 39 (.leaf (7)) (.leaf (0)))) (.branch 41 (.leaf (2)) (.branch 42 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2233
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 32 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 36 (.leaf (9)) (.branch 40 (.leaf (10)) (.leaf (11)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 38 (.leaf (9)) (.branch 42 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-32)) (.leaf (-39)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-17)) (.leaf (-19)))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (-31)) (.leaf (-32)))),
  (.branch 17 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 29 (.branch 21 (.branch 17 (.leaf (-39)) (.leaf (-38))) (.branch 25 (.leaf (-37)) (.leaf (-36)))) (.branch 37 (.branch 33 (.leaf (-35)) (.leaf (-34))) (.branch 41 (.leaf (-33)) (.branch 42 (.leaf (-22)) (.leaf (-11)))))),
  (.leaf (-2)),
  (.branch 36 (.leaf (-7)) (.branch 42 (.leaf (-6)) (.leaf (-4)))),
  (.branch 40 (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-16)) (.leaf (-13)))) (.branch 41 (.leaf (-10)) (.branch 42 (.leaf (-7)) (.leaf (-4))))),
  (.branch 37 (.branch 34 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-16)) (.leaf (-14))))) (.branch 40 (.branch 38 (.leaf (-12)) (.branch 39 (.leaf (-10)) (.leaf (-8)))) (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 35 (.branch 31 (.branch 29 (.branch 28 (.leaf (-32)) (.leaf (-30))) (.branch 30 (.leaf (-28)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-22))) (.branch 34 (.leaf (-20)) (.leaf (-18))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-14))) (.branch 38 (.leaf (-12)) (.leaf (-10)))) (.branch 41 (.branch 40 (.leaf (-8)) (.leaf (-6))) (.branch 42 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 40 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 41 (.leaf (-6)) (.branch 42 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_200_2234 : CycleWitness 8 where
  length := 42
  word := (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (0)))) (.branch 17 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 24 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (6))) (.branch 41 (.leaf (0)) (.leaf (7))))))
  code := certificateD8_2234
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 7 (.branch 5 (.leaf (4)) (.leaf (5))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (7)) (.leaf (8)))))) (.branch 15 (.branch 13 (.branch 11 (.leaf (9)) (.leaf (10))) (.branch 14 (.leaf (11)) (.leaf (12)))) (.branch 17 (.branch 16 (.leaf (13)) (.leaf (14))) (.branch 19 (.leaf (15)) (.branch 20 (.leaf (16)) (.leaf (17))))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (18)) (.leaf (19))) (.branch 25 (.leaf (20)) (.leaf (21)))) (.branch 28 (.branch 27 (.leaf (22)) (.leaf (23))) (.branch 29 (.leaf (24)) (.branch 31 (.leaf (25)) (.leaf (26)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (27)) (.leaf (28))) (.branch 35 (.leaf (29)) (.leaf (30)))) (.branch 39 (.branch 38 (.leaf (31)) (.leaf (32))) (.branch 40 (.leaf (33)) (.branch 41 (.leaf (34)) (.leaf (35)))))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))) (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-36))),
  (.branch 12 (.leaf (0)) (.leaf (-30))),
  (.branch 18 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-12))),
  (.branch 36 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-5)),
  (.branch 24 (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-36)) (.leaf (-35))) (.branch 9 (.leaf (-34)) (.leaf (-33)))) (.branch 12 (.branch 11 (.leaf (-32)) (.leaf (-31))) (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))) (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))) (.branch 27 (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_200_2235 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (6)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (7))))))) (.branch 32 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (6)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (5)) (.leaf (0))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2235
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 18 (.leaf (10)) (.leaf (11)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14)))) (.branch 27 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 36 (.branch 32 (.leaf (18)) (.branch 34 (.leaf (19)) (.leaf (20)))) (.branch 39 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 41 (.leaf (23)) (.leaf (24))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 17 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 38 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_200_2236 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (6))))))) (.branch 32 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (5)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (3)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2236
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 18 (.leaf (10)) (.leaf (11)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14)))) (.branch 27 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 36 (.branch 32 (.leaf (18)) (.branch 34 (.leaf (19)) (.leaf (20)))) (.branch 39 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 41 (.leaf (23)) (.leaf (24))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 21 (.leaf (0)) (.leaf (-21))),
  (.leaf (0))]
  high := ![(.branch 38 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-17))))) (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_200_2237 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (0))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (3))))))) (.branch 32 (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (0)))) (.branch 39 (.branch 38 (.leaf (2)) (.leaf (0))) (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2237
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 18 (.leaf (10)) (.leaf (11)))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14)))) (.branch 27 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 36 (.branch 32 (.leaf (18)) (.branch 34 (.leaf (19)) (.leaf (20)))) (.branch 39 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 41 (.leaf (23)) (.leaf (24))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-30))),
  (.branch 26 (.leaf (0)) (.leaf (-16))),
  (.branch 40 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))) (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_200_2238 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 7 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2))))))) (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (7)) (.branch 26 (.leaf (0)) (.leaf (4))))) (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (3)) (.branch 31 (.leaf (1)) (.leaf (0)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (5)) (.leaf (0))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (4)) (.leaf (0))))) (.branch 39 (.branch 38 (.leaf (1)) (.leaf (3))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2238
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 23 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 23 (.leaf (-24)) (.leaf (-29)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 39 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (-5))) (.branch 36 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (-4)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-38))),
  (.branch 25 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 38 (.leaf (-26)) (.branch 41 (.leaf (-24)) (.leaf (-17))))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3)))),
  (.branch 39 (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-7)),
  (.branch 23 (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-38)) (.leaf (-37))) (.branch 7 (.leaf (-36)) (.leaf (-35)))) (.branch 10 (.branch 9 (.leaf (-34)) (.leaf (-33))) (.branch 11 (.leaf (-32)) (.branch 12 (.leaf (-31)) (.leaf (-30)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.branch 17 (.leaf (-26)) (.leaf (-25))))) (.branch 20 (.branch 19 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20))))))) (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_200_2239 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (0))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (5))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (7)) (.leaf (2))))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (7)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_2239
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.leaf (15)))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 19 (.leaf (-30)) (.leaf (-32)))),
  (.leaf (0)),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 20 (.leaf (-14)) (.branch 32 (.leaf (-20)) (.leaf (-22))))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-9)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.branch 41 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 29 (.branch 23 (.branch 20 (.leaf (-32)) (.leaf (-31))) (.branch 26 (.leaf (-30)) (.leaf (-29)))) (.branch 35 (.branch 32 (.leaf (-28)) (.leaf (-27))) (.branch 38 (.leaf (-26)) (.branch 41 (.leaf (-25)) (.leaf (-17)))))),
  (.leaf (0)),
  (.branch 40 (.branch 33 (.leaf (-22)) (.leaf (-19))) (.branch 41 (.leaf (-15)) (.leaf (-11)))),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-9)))) (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))))),
  (.leaf (-4)),
  (.branch 33 (.branch 29 (.branch 27 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_200_2240 : CycleWitness 8 where
  length := 42
  word := (.branch 22 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (5))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 17 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4))))) (.branch 19 (.branch 18 (.leaf (7)) (.leaf (0))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 32 (.branch 27 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 28 (.leaf (0)) (.leaf (6))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (0)) (.leaf (4)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (5)) (.branch 36 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (3))) (.branch 40 (.leaf (7)) (.branch 41 (.leaf (0)) (.leaf (1))))))))
  code := certificateD8_2240
  counts := ![(.branch 19 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 28 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 37 (.leaf (-14)) (.leaf (-19)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 35 (.leaf (-13)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.branch 29 (.leaf (-12)) (.leaf (-13)))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 34 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 39 (.leaf (-14)) (.leaf (-11)))),
  (.branch 35 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 38 (.leaf (-19)) (.leaf (-16))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 36 (.leaf (-17)) (.branch 37 (.leaf (-15)) (.leaf (-13)))) (.branch 40 (.branch 39 (.leaf (-11)) (.leaf (-9))) (.branch 41 (.leaf (-7)) (.leaf (-5))))),
  (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_200_2241 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (7)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_2241
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 35 (.branch 18 (.leaf (-10)) (.leaf (-11))) (.branch 39 (.leaf (-12)) (.leaf (-13))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 30 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 41 (.leaf (-6)) (.leaf (-3))),
  (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 39 (.branch 26 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 40 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_200_2242 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_2242
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-8))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 41 (.leaf (-6)) (.leaf (-3))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_200_2243 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_2243
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 23 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-11)))) (.branch 26 (.leaf (-12)) (.branch 30 (.leaf (-13)) (.leaf (-14))))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-26))),
  (.branch 37 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 40 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 26 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 22 (.branch 19 (.branch 17 (.leaf (-26)) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 20 (.leaf (-23)) (.branch 21 (.leaf (-22)) (.leaf (-21))))) (.branch 25 (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18)))) (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))))) (.branch 35 (.branch 32 (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))) (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_200_2244 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_2244
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 18 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-35))),
  (.branch 28 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-35)) (.leaf (-34))) (.branch 10 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.branch 12 (.leaf (-31)) (.leaf (-30))) (.branch 14 (.leaf (-29)) (.leaf (-28))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24)))) (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))))) (.branch 33 (.branch 28 (.branch 26 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 30 (.branch 29 (.leaf (-14)) (.leaf (-13))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_200_2245 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (6))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (5)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_2245
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 35 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 25 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 38 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-18)))) (.branch 24 (.leaf (-21)) (.branch 27 (.leaf (-24)) (.leaf (-27))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))) (.branch 20 (.leaf (-3)) (.branch 41 (.leaf (-5)) (.leaf (-6))))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-21))),
  (.leaf (0))]
  high := ![(.branch 36 (.branch 28 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25)))) (.branch 40 (.leaf (-24)) (.branch 41 (.leaf (-20)) (.leaf (-16))))),
  (.branch 24 (.leaf (-11)) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-6)),
  (.branch 39 (.branch 27 (.leaf (-11)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-17))))) (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_200_2246 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (7)))) (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (7)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2246
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.branch 41 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 25 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 36 (.leaf (-15)) (.leaf (-18)))),
  (.branch 29 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 37 (.leaf (-10)) (.leaf (-11)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 36 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.branch 39 (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-16)) (.leaf (-14)))) (.branch 40 (.leaf (-12)) (.branch 41 (.leaf (-10)) (.leaf (-8))))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-9))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 17 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_200_2247 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2247
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 27 (.leaf (-8)) (.branch 37 (.leaf (-9)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 41 (.leaf (-6)) (.leaf (-3))),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_200_2248 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (7)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2248
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-7)) (.branch 26 (.leaf (-9)) (.leaf (-10))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))) (.branch 18 (.leaf (-11)) (.branch 39 (.leaf (-13)) (.leaf (-14))))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 38 (.leaf (-5)) (.leaf (-7)))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 30 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 40 (.branch 39 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (-1)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_200_2249 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (7)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (2))))))))
  code := certificateD8_2249
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 33 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 32 (.leaf (-15)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-5))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 30 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 41 (.leaf (-6)) (.leaf (-3))),
  (.branch 40 (.branch 29 (.leaf (-14)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16))))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_200_2250 : CycleWitness 8 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (5)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2250
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 33 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.branch 41 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 29 (.leaf (-16)) (.leaf (-23)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-12)) (.leaf (-25)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.branch 36 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))),
  (.branch 35 (.branch 30 (.leaf (-23)) (.leaf (-22))) (.branch 40 (.leaf (-21)) (.branch 41 (.leaf (-16)) (.leaf (-11))))),
  (.branch 33 (.leaf (-25)) (.branch 41 (.leaf (-22)) (.leaf (-17)))),
  (.branch 38 (.branch 26 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 24 (.branch 21 (.branch 19 (.leaf (-24)) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-19))))) (.branch 27 (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))))) (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_200 : Fin 23 → CycleWitness 8 := ![witnessD8_200_2228, witnessD8_200_2229, witnessD8_200_2230, witnessD8_200_2231, witnessD8_200_2232, witnessD8_200_2233, witnessD8_200_2234, witnessD8_200_2235, witnessD8_200_2236, witnessD8_200_2237, witnessD8_200_2238, witnessD8_200_2239, witnessD8_200_2240, witnessD8_200_2241, witnessD8_200_2242, witnessD8_200_2243, witnessD8_200_2244, witnessD8_200_2245, witnessD8_200_2246, witnessD8_200_2247, witnessD8_200_2248, witnessD8_200_2249, witnessD8_200_2250]
end RealPinwheel.FiveSixths


