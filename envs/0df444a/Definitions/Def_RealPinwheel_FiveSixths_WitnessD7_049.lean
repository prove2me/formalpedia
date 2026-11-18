-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_049
-- name    : RealPinwheel_FiveSixths_WitnessD7_049
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:56:54.047836+00:00
-- url     : https://prove2.me/theorems/c54406aa-2164-41de-a2f2-0a1a84fac6e7
-- title:
--   Exact witness block D7_049
-- statement:
--   These exact witnesses represent words 777 through 803 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 777–803; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_049_776 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (3)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (6)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (4)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_776
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.branch 34 (.leaf (-5)) (.leaf (-6))))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-35))),
  (.branch 22 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 37 (.leaf (-4)) (.leaf (-2))),
  (.branch 20 (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-35)) (.leaf (-34))) (.branch 6 (.leaf (-33)) (.leaf (-32)))) (.branch 9 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 10 (.leaf (-29)) (.leaf (-28))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-27)) (.leaf (-26))) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-14)) (.leaf (-13))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_049_777 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (5)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (6))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_777
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 27 (.leaf (-26)) (.leaf (-37)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 12 (.leaf (-27)) (.leaf (-30)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.branch 36 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-29)) (.leaf (-30)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 32 (.branch 28 (.leaf (-37)) (.leaf (-36))) (.branch 36 (.leaf (-35)) (.branch 37 (.leaf (-26)) (.leaf (-17))))),
  (.branch 35 (.branch 13 (.leaf (-30)) (.branch 24 (.leaf (-29)) (.leaf (-28)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 15 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 23 (.leaf (-5)) (.branch 31 (.leaf (-4)) (.leaf (0))))),
  (.branch 37 (.leaf (-6)) (.leaf (-3))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-30)) (.leaf (-27))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_049_778 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_778
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))) (.branch 26 (.leaf (-8)) (.branch 32 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 29 (.leaf (-12)) (.leaf (-15)))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 21 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 35 (.branch 33 (.leaf (-10)) (.branch 34 (.leaf (-9)) (.leaf (-8)))) (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5))))),
  (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-14))) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))))),
  (.leaf (-1))]
def witnessD7_049_779 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (6)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (5)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_779
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 30 (.leaf (-10)) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_049_780 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (6))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_780
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 23 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-28))) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-8)))),
  (.branch 36 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 25 (.leaf (-32)) (.branch 33 (.leaf (-30)) (.leaf (-25)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-15))) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.branch 6 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 32 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_049_781 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (5)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (5))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_781
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-31))) (.branch 22 (.leaf (-34)) (.leaf (-36)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-8)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 35 (.branch 23 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-28)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.leaf (-5)) (.leaf (-3))),
  (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_049_782 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (5)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_782
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 25 (.leaf (-18)) (.leaf (-25)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-5)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.leaf (-6)) (.leaf (-3))),
  (.branch 35 (.branch 26 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-22)))) (.branch 36 (.leaf (-20)) (.branch 37 (.leaf (-18)) (.leaf (-16))))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_049_783 : CycleWitness 7 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (4)) (.leaf (0)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (1))) (.branch 35 (.leaf (4)) (.branch 36 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_783
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 14 (.leaf (-5)) (.branch 27 (.leaf (-6)) (.leaf (-8))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-6)) (.leaf (-8))))]
  high := ![(.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4))))),
  (.branch 29 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-7)) (.leaf (-5))))),
  (.branch 32 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 5 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-6)))),
  (.branch 17 (.leaf (-10)) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 9 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_049_784 : CycleWitness 7 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (5))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (6)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (3)) (.leaf (0))))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (5))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_784
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-22))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 31 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-5)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-21)))]
  high := ![(.leaf (-4)),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-4))))),
  (.branch 34 (.branch 4 (.leaf (-22)) (.branch 19 (.leaf (-21)) (.leaf (-20)))) (.branch 35 (.leaf (-15)) (.branch 36 (.leaf (-10)) (.leaf (-5))))),
  (.branch 34 (.branch 32 (.leaf (-14)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-6)) (.leaf (-4))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.leaf (-4)))),
  (.branch 31 (.branch 28 (.branch 9 (.leaf (-21)) (.leaf (-20))) (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-16)) (.leaf (-14))))) (.branch 34 (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-10)) (.leaf (-8)))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_049_785 : CycleWitness 7 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (2)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (5))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (0)) (.leaf (4))))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_785
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 21 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 23 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 34 (.leaf (-23)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-14)) (.leaf (-22)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 22 (.leaf (-6)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-25)) (.leaf (-26)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 35 (.leaf (-26)) (.branch 36 (.leaf (-20)) (.leaf (-14)))),
  (.branch 21 (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-12))))),
  (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-7))) (.branch 36 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (-4)),
  (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4))))),
  (.branch 32 (.branch 30 (.branch 17 (.leaf (-26)) (.leaf (-24))) (.branch 31 (.leaf (-21)) (.leaf (-18)))) (.branch 34 (.branch 33 (.leaf (-15)) (.leaf (-12))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 25 (.leaf (-2)) (.leaf (0)))]
def witnessD7_049_786 : CycleWitness 7 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (5)) (.leaf (3))))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (6)) (.branch 36 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_786
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 16 (.leaf (-12)) (.branch 29 (.leaf (-13)) (.leaf (-14))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-12)) (.branch 27 (.leaf (-13)) (.leaf (-21))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.branch 23 (.leaf (-5)) (.leaf (-6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-22))) (.branch 32 (.leaf (-24)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-13)))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.branch 30 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-11)) (.leaf (-9)))),
  (.branch 34 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 35 (.leaf (-17)) (.branch 36 (.leaf (-14)) (.leaf (-11))))),
  (.branch 31 (.branch 24 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-20))) (.branch 35 (.leaf (-15)) (.branch 36 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-11)) (.leaf (-9)))) (.branch 35 (.leaf (-7)) (.branch 36 (.leaf (-5)) (.leaf (-3))))),
  (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_049_787 : CycleWitness 7 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (2)) (.leaf (3)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (1))) (.branch 35 (.leaf (6)) (.branch 36 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_787
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 23 (.leaf (-10)) (.leaf (-11)))),
  (.branch 26 (.leaf (0)) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-23)) (.leaf (-24)))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.branch 13 (.leaf (-20)) (.branch 17 (.leaf (-19)) (.leaf (-18)))) (.branch 29 (.branch 25 (.leaf (-17)) (.leaf (-16))) (.branch 33 (.leaf (-15)) (.leaf (-14))))),
  (.branch 35 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-7)) (.leaf (-4)))),
  (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-10))) (.branch 36 (.leaf (-8)) (.leaf (-6)))),
  (.branch 33 (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.leaf (-3))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-24)) (.branch 27 (.leaf (-22)) (.leaf (-20)))) (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-16)) (.leaf (-14))))) (.branch 34 (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-10)) (.leaf (-8)))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-3)) (.leaf (-2))))]
def witnessD7_049_788 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 11 (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (6)) (.leaf (0)))) (.branch 30 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (4))))))
  code := certificateD7_788
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (6))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (8))) (.branch 11 (.leaf (9)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (11)) (.leaf (12))) (.branch 16 (.leaf (13)) (.leaf (14)))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (15)) (.leaf (16))) (.branch 21 (.leaf (17)) (.leaf (18)))) (.branch 25 (.branch 23 (.leaf (19)) (.leaf (20))) (.branch 26 (.leaf (21)) (.leaf (22))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (24))) (.branch 31 (.leaf (25)) (.leaf (26)))) (.branch 34 (.branch 33 (.leaf (27)) (.leaf (28))) (.branch 35 (.leaf (29)) (.leaf (30))))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))) (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 24 (.leaf (0)) (.leaf (-12)))]
  high := ![(.leaf (-5)),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_049_789 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 14 (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (4)))))) (.branch 27 (.branch 23 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 32 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_789
  counts := ![(.branch 17 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.leaf (9)) (.branch 16 (.leaf (10)) (.leaf (11)))))) (.branch 26 (.branch 22 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 23 (.leaf (15)) (.branch 25 (.leaf (16)) (.leaf (17))))) (.branch 31 (.branch 28 (.leaf (18)) (.branch 29 (.leaf (19)) (.leaf (20)))) (.branch 34 (.branch 32 (.leaf (21)) (.leaf (22))) (.branch 35 (.leaf (23)) (.leaf (24))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-21))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.leaf (-2)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_049_790 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 14 (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (2)))))) (.branch 27 (.branch 23 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 32 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_790
  counts := ![(.branch 17 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.leaf (9)) (.branch 16 (.leaf (10)) (.leaf (11)))))) (.branch 26 (.branch 22 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 23 (.leaf (15)) (.branch 25 (.leaf (16)) (.leaf (17))))) (.branch 31 (.branch 28 (.leaf (18)) (.branch 29 (.leaf (19)) (.leaf (20)))) (.branch 34 (.branch 32 (.leaf (21)) (.leaf (22))) (.branch 35 (.leaf (23)) (.leaf (24))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 24 (.leaf (0)) (.leaf (-12))),
  (.branch 33 (.leaf (0)) (.leaf (-3))),
  (.branch 15 (.leaf (0)) (.leaf (-21)))]
  high := ![(.leaf (-2)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_049_791 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.leaf (0)))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_791
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 25 (.leaf (12)) (.leaf (13))))) (.branch 30 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-15))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_049_792 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_792
  counts := ![(.branch 17 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 24 (.leaf (12)) (.leaf (13))))) (.branch 30 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 32 (.leaf (16)) (.branch 35 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_049_793 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (5)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (2)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_793
  counts := ![(.branch 17 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.branch 24 (.leaf (13)) (.leaf (14))))) (.branch 31 (.branch 28 (.leaf (15)) (.branch 30 (.leaf (16)) (.leaf (17)))) (.branch 33 (.leaf (18)) (.branch 35 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_049_794 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (6)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (2)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (5)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_794
  counts := ![(.branch 17 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.branch 24 (.leaf (13)) (.leaf (14))))) (.branch 31 (.branch 28 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17)))) (.branch 33 (.leaf (18)) (.branch 35 (.leaf (19)) (.leaf (20))))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 23 (.leaf (0)) (.leaf (-13))),
  (.branch 32 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 32 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 35 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_049_795 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (6))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_795
  counts := ![(.branch 17 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 24 (.leaf (12)) (.leaf (13))))) (.branch 31 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 33 (.leaf (16)) (.branch 35 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_049_796 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (6)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_796
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 22 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 30 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 32 (.leaf (-7)) (.leaf (-5))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_049_797 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.leaf (6)))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (5))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_797
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 25 (.leaf (12)) (.leaf (13))))) (.branch 31 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_049_798 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (6)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_798
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 22 (.leaf (-10)) (.leaf (-11))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-21)) (.leaf (-22)))) (.branch 24 (.leaf (-23)) (.branch 31 (.leaf (-24)) (.leaf (-25))))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 30 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-7)) (.leaf (-5))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_049_799 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (4)) (.leaf (1)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (1))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (6)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_799
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 29 (.leaf (-10)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-23))),
  (.branch 31 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_049_800 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (2))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (6))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_800
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 30 (.leaf (-6)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 24 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-21))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 32 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 22 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 31 (.leaf (-8)) (.leaf (-7))),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_049_801 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.leaf (6)))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_801
  counts := ![(.branch 17 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.leaf (15)))))),
  (.branch 19 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.branch 26 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 27 (.leaf (-8)) (.branch 35 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_049_802 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_802
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_049 : Fin 27 → CycleWitness 7 := ![witnessD7_049_776, witnessD7_049_777, witnessD7_049_778, witnessD7_049_779, witnessD7_049_780, witnessD7_049_781, witnessD7_049_782, witnessD7_049_783, witnessD7_049_784, witnessD7_049_785, witnessD7_049_786, witnessD7_049_787, witnessD7_049_788, witnessD7_049_789, witnessD7_049_790, witnessD7_049_791, witnessD7_049_792, witnessD7_049_793, witnessD7_049_794, witnessD7_049_795, witnessD7_049_796, witnessD7_049_797, witnessD7_049_798, witnessD7_049_799, witnessD7_049_800, witnessD7_049_801, witnessD7_049_802]
end RealPinwheel.FiveSixths


