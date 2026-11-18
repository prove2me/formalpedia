-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_039
-- name    : RealPinwheel_FiveSixths_WitnessD7_039
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:47:34.751201+00:00
-- url     : https://prove2.me/theorems/dad946b8-462a-4562-9b25-efd5b1384c7d
-- title:
--   Exact witness block D7_039
-- statement:
--   These exact witnesses represent words 537 through 558 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 537–558; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_039_536 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_536
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 28 (.leaf (-7)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-24))),
  (.branch 42 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.leaf (-8)) (.leaf (-5))),
  (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 26 (.branch 23 (.branch 21 (.leaf (-24)) (.branch 22 (.leaf (-23)) (.leaf (-22)))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19))))) (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_039_537 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_537
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 28 (.leaf (-7)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.leaf (-8)) (.leaf (-5))),
  (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 39 (.branch 23 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_039_538 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_538
  counts := ![(.branch 21 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 17 (.leaf (8)) (.branch 19 (.leaf (9)) (.leaf (10)))))) (.branch 33 (.branch 27 (.branch 23 (.leaf (11)) (.branch 25 (.leaf (12)) (.leaf (13)))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))) (.branch 39 (.branch 35 (.leaf (17)) (.branch 37 (.leaf (18)) (.leaf (19)))) (.branch 41 (.leaf (20)) (.branch 43 (.leaf (21)) (.leaf (22))))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-13)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 32 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-32))),
  (.branch 34 (.leaf (0)) (.leaf (-10)))]
  high := ![(.leaf (-1)),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-11)) (.branch 43 (.leaf (-10)) (.leaf (-7))))),
  (.branch 41 (.branch 33 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-4))))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 28 (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-32)) (.leaf (-31))) (.branch 15 (.leaf (-30)) (.leaf (-29)))) (.branch 18 (.branch 17 (.leaf (-28)) (.leaf (-27))) (.branch 19 (.leaf (-26)) (.leaf (-25))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-24)) (.leaf (-23))) (.branch 23 (.leaf (-22)) (.leaf (-21)))) (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.leaf (-17)))))) (.branch 36 (.branch 32 (.branch 30 (.branch 29 (.leaf (-16)) (.leaf (-15))) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-6))))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_039_539 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (6)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_539
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 30 (.leaf (12)) (.leaf (13))))) (.branch 37 (.branch 35 (.leaf (14)) (.leaf (15))) (.branch 40 (.leaf (16)) (.branch 42 (.leaf (17)) (.leaf (18))))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 43 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 5 (.leaf (-17)) (.leaf (-21)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-3)) (.branch 31 (.leaf (-4)) (.leaf (-5))))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-33))),
  (.branch 33 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 33 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-5)),
  (.branch 42 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-33)) (.leaf (-32))) (.branch 14 (.leaf (-31)) (.leaf (-30)))) (.branch 17 (.branch 16 (.leaf (-29)) (.leaf (-28))) (.branch 18 (.leaf (-27)) (.leaf (-26))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-25)) (.leaf (-24))) (.branch 22 (.leaf (-23)) (.leaf (-22)))) (.branch 25 (.branch 24 (.leaf (-21)) (.leaf (-20))) (.branch 26 (.leaf (-19)) (.leaf (-18)))))) (.branch 35 (.branch 31 (.branch 29 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 30 (.leaf (-15)) (.leaf (-14)))) (.branch 33 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 34 (.leaf (-11)) (.leaf (-10))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_039_540 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (6)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (4))))))))
  code := certificateD7_540
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 33 (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 30 (.leaf (12)) (.leaf (13))))) (.branch 37 (.branch 35 (.leaf (14)) (.leaf (15))) (.branch 40 (.leaf (16)) (.branch 42 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-17)) (.leaf (-19)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 34 (.branch 19 (.leaf (-4)) (.leaf (-5))) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (-23)) (.leaf (-24)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 38 (.leaf (-19)) (.branch 43 (.leaf (-18)) (.leaf (-9)))),
  (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 40 (.branch 27 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-21))) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_039_541 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_541
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 19 (.leaf (-6)) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-23))),
  (.branch 43 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 37 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.leaf (-4)))),
  (.branch 42 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-4)))),
  (.branch 36 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 41 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19))))) (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_039_542 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_542
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 33 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 11 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-11)))) (.branch 37 (.leaf (-13)) (.branch 41 (.leaf (-15)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-26))),
  (.branch 40 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 37 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-14)) (.leaf (-11)))),
  (.branch 33 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 39 (.leaf (-5)) (.branch 40 (.leaf (-2)) (.leaf (0))))),
  (.branch 28 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 24 (.branch 21 (.branch 19 (.leaf (-26)) (.branch 20 (.leaf (-25)) (.leaf (-24)))) (.branch 22 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-21))))) (.branch 27 (.branch 25 (.leaf (-20)) (.branch 26 (.leaf (-19)) (.leaf (-18)))) (.branch 29 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 30 (.leaf (-15)) (.leaf (-14)))))) (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_039_543 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (5)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (5)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (3))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (6)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_543
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 33 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 11 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-11)))) (.branch 37 (.leaf (-13)) (.branch 41 (.leaf (-15)) (.leaf (-17))))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 37 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 43 (.leaf (-8)) (.leaf (-4))))),
  (.branch 42 (.leaf (-17)) (.branch 43 (.leaf (-14)) (.leaf (-11)))),
  (.branch 33 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 39 (.leaf (-5)) (.branch 40 (.leaf (-2)) (.leaf (0))))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.leaf (-7)))) (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_039_544 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (5)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (6)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (6)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_544
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 27 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 41 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 16 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 6 (.leaf (-8)) (.leaf (-9)))) (.branch 25 (.branch 19 (.leaf (-10)) (.leaf (-11))) (.branch 34 (.leaf (-13)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 26 (.leaf (-3)) (.branch 37 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 39 (.branch 35 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-12)))),
  (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))),
  (.branch 40 (.branch 38 (.leaf (-5)) (.branch 39 (.leaf (-4)) (.leaf (-3)))) (.branch 41 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))),
  (.branch 21 (.branch 6 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.leaf (-7)))),
  (.branch 40 (.branch 10 (.leaf (-17)) (.branch 25 (.leaf (-16)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_039_545 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (3)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (3))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (3)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_545
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 23 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 43 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-5)))) (.branch 25 (.leaf (-6)) (.branch 36 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-12))) (.branch 19 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-35))),
  (.branch 31 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.leaf (-4)) (.branch 40 (.leaf (-3)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-35)) (.leaf (-34))) (.branch 12 (.leaf (-33)) (.leaf (-32)))) (.branch 15 (.branch 14 (.leaf (-31)) (.leaf (-30))) (.branch 16 (.leaf (-29)) (.leaf (-28))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-27)) (.leaf (-26))) (.branch 20 (.leaf (-25)) (.leaf (-24)))) (.branch 23 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19))))))) (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_039_546 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_546
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 24 (.leaf (5)) (.branch 29 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 35 (.leaf (3)) (.branch 44 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 19 (.leaf (-6)) (.branch 41 (.leaf (-7)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 37 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.leaf (-4)))),
  (.branch 42 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-4)))),
  (.branch 41 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_039_547 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (3)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (5))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (5)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_547
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 40 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 40 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.leaf (-4)))),
  (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-13))) (.branch 43 (.leaf (-10)) (.leaf (-7)))),
  (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))),
  (.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))),
  (.branch 39 (.branch 36 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_039_548 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (6)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (5))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (6)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_548
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 18 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 28 (.branch 4 (.leaf (0)) (.leaf (-17))) (.branch 35 (.leaf (-19)) (.leaf (-30)))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-4)) (.leaf (-6))))]
  high := ![(.branch 19 (.leaf (-9)) (.branch 39 (.leaf (-8)) (.leaf (-5)))),
  (.branch 41 (.branch 20 (.leaf (-14)) (.branch 40 (.leaf (-13)) (.leaf (-11)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-7)) (.leaf (-5))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-30)) (.leaf (-28))) (.branch 38 (.leaf (-26)) (.leaf (-24)))) (.branch 41 (.branch 40 (.leaf (-22)) (.leaf (-20))) (.branch 42 (.leaf (-18)) (.branch 43 (.leaf (-16)) (.leaf (-14)))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 23 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 41 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_039_549 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (6)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (4)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_549
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 40 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 18 (.leaf (-8)) (.leaf (-9))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))) (.branch 28 (.leaf (-7)) (.branch 39 (.leaf (-8)) (.leaf (-9))))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-32)) (.leaf (-33)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 41 (.leaf (-9)) (.leaf (-5))),
  (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-33)) (.leaf (-30))) (.branch 36 (.leaf (-27)) (.branch 37 (.leaf (-24)) (.leaf (-21))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 27 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 23 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 38 (.leaf (-21)) (.leaf (-18)))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))))]
def witnessD7_039_550 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_550
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 40 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 7 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-24))),
  (.branch 42 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 41 (.leaf (-9)) (.leaf (-5))),
  (.branch 42 (.branch 36 (.leaf (-7)) (.leaf (-6))) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 26 (.branch 23 (.branch 21 (.leaf (-24)) (.branch 22 (.leaf (-23)) (.leaf (-22)))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19))))) (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_039_551 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (6)) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (0)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_551
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 30 (.leaf (13)) (.leaf (14))))) (.branch 39 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 41 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-26)) (.leaf (-28)))),
  (.branch 13 (.leaf (0)) (.branch 42 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 28 (.leaf (-8)) (.branch 37 (.leaf (-7)) (.leaf (-5)))),
  (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-15)) (.leaf (-12)))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 39 (.branch 36 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-21)) (.leaf (-18))))) (.branch 41 (.branch 40 (.leaf (-15)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 43 (.leaf (-6)) (.leaf (-3)))]
def witnessD7_039_552 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (2)) (.leaf (1)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (3)) (.leaf (0)))) (.branch 42 (.leaf (4)) (.branch 43 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_552
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 41 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 30 (.leaf (9)) (.leaf (10)))) (.branch 39 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-17)))) (.branch 25 (.leaf (-18)) (.branch 28 (.leaf (-19)) (.leaf (-20))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))) (.branch 17 (.leaf (-8)) (.branch 39 (.leaf (-11)) (.leaf (-13))))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 20 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-35))),
  (.branch 31 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 42 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-14)) (.leaf (-9)))),
  (.branch 40 (.leaf (-13)) (.leaf (-9))),
  (.branch 37 (.leaf (-2)) (.leaf (0))),
  (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-35)) (.leaf (-34))) (.branch 12 (.leaf (-33)) (.leaf (-32)))) (.branch 15 (.branch 14 (.leaf (-31)) (.leaf (-30))) (.branch 16 (.leaf (-29)) (.leaf (-28))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-27)) (.leaf (-26))) (.branch 20 (.leaf (-25)) (.leaf (-24)))) (.branch 23 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19))))))) (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_039_553 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (0)) (.leaf (6)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (1)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (3)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (6)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (1)) (.leaf (3)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_553
  counts := ![(.branch 20 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 42 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 25 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-15)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-20)) (.leaf (-22))))]
  high := ![(.branch 39 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 43 (.leaf (-14)) (.leaf (-9)))),
  (.branch 41 (.branch 34 (.leaf (-15)) (.leaf (-13))) (.branch 42 (.leaf (-10)) (.branch 43 (.leaf (-7)) (.leaf (-4))))),
  (.branch 37 (.leaf (-6)) (.leaf (-4))),
  (.branch 42 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 38 (.branch 23 (.leaf (-22)) (.leaf (-21))) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3)))))]
def witnessD7_039_554 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (4)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (4))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (3)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_554
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 19 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 24 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 41 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (-8))) (.branch 35 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 40 (.branch 37 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.leaf (-4)))),
  (.branch 42 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 27 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 37 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-8)) (.leaf (-7)))) (.branch 41 (.branch 40 (.leaf (-6)) (.leaf (-5))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD7_039_555 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (6)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (2)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (6)) (.leaf (4))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (4)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (6)) (.branch 43 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_555
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 41 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 25 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 34 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 22 (.branch 15 (.leaf (0)) (.leaf (-1))) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 42 (.branch 26 (.leaf (-21)) (.leaf (-20))) (.branch 43 (.leaf (-14)) (.leaf (-8)))),
  (.branch 41 (.branch 35 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-13)) (.branch 43 (.leaf (-10)) (.leaf (-7))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 40 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.branch 28 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-11))) (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-9)) (.leaf (-8))))) (.branch 41 (.branch 39 (.leaf (-7)) (.branch 40 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 27 (.leaf (-4)) (.branch 43 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_039_556 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (3)) (.branch 40 (.leaf (1)) (.leaf (0)))) (.branch 42 (.leaf (2)) (.branch 43 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_556
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 41 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 34 (.branch 27 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 30 (.leaf (9)) (.leaf (10)))) (.branch 40 (.branch 37 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-18)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-33))),
  (.branch 33 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 42 (.leaf (-21)) (.branch 43 (.leaf (-14)) (.leaf (-7)))),
  (.branch 31 (.leaf (-10)) (.leaf (-7))),
  (.branch 37 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-33)) (.leaf (-32))) (.branch 14 (.leaf (-31)) (.leaf (-30)))) (.branch 17 (.branch 16 (.leaf (-29)) (.leaf (-28))) (.branch 18 (.leaf (-27)) (.leaf (-26))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-25)) (.leaf (-24))) (.branch 22 (.leaf (-23)) (.leaf (-22)))) (.branch 25 (.branch 24 (.leaf (-21)) (.leaf (-20))) (.branch 26 (.leaf (-19)) (.leaf (-18)))))) (.branch 35 (.branch 31 (.branch 29 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 30 (.leaf (-15)) (.leaf (-14)))) (.branch 33 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 34 (.leaf (-11)) (.leaf (-10))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_039_557 : CycleWitness 7 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (5)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (4)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (6)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_557
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 38 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 39 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-25))),
  (.branch 41 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 38 (.branch 35 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 39 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-10))) (.branch 42 (.leaf (-8)) (.branch 43 (.leaf (-6)) (.leaf (-4))))),
  (.branch 37 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 20 (.leaf (-25)) (.branch 21 (.leaf (-24)) (.leaf (-23)))) (.branch 23 (.leaf (-22)) (.branch 24 (.leaf (-21)) (.leaf (-20))))) (.branch 28 (.branch 26 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 29 (.leaf (-16)) (.branch 30 (.leaf (-15)) (.leaf (-14)))))) (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_039 : Fin 22 → CycleWitness 7 := ![witnessD7_039_536, witnessD7_039_537, witnessD7_039_538, witnessD7_039_539, witnessD7_039_540, witnessD7_039_541, witnessD7_039_542, witnessD7_039_543, witnessD7_039_544, witnessD7_039_545, witnessD7_039_546, witnessD7_039_547, witnessD7_039_548, witnessD7_039_549, witnessD7_039_550, witnessD7_039_551, witnessD7_039_552, witnessD7_039_553, witnessD7_039_554, witnessD7_039_555, witnessD7_039_556, witnessD7_039_557]
end RealPinwheel.FiveSixths


