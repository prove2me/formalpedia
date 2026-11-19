-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_241
-- name    : RealPinwheel_FiveSixths_WitnessD8_241
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:25:13.187413+00:00
-- url     : https://prove2.me/theorems/978f992a-9355-493e-a8f8-820005c856f4
-- title:
--   Exact witness block D8_241
-- statement:
--   These exact witnesses represent words 3368 through 3405 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3368–3405; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_241_3367 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (3)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3367
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 25 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.branch 3 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17)))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 12 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_241_3368 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (2))) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (4))) (.branch 26 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3368
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 14 (.leaf (-5)) (.branch 22 (.leaf (-6)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4))))),
  (.branch 14 (.branch 3 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 12 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_241_3369 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3369
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 16 (.leaf (0)) (.leaf (-11))),
  (.branch 25 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 19 (.leaf (-18)) (.leaf (-15))) (.branch 26 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16))))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_241_3370 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (7))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (3))) (.branch 26 (.leaf (2)) (.leaf (1)))))))
  code := certificateD8_3370
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.branch 25 (.leaf (-1)) (.leaf (0))))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.branch 4 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 9 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17))))) (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_241_3371 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (4)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (2)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (4)) (.branch 22 (.leaf (7)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (5)))))))
  code := certificateD8_3371
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 6 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-10))))),
  (.branch 24 (.branch 18 (.leaf (-24)) (.leaf (-23))) (.branch 25 (.leaf (-19)) (.branch 26 (.leaf (-15)) (.leaf (-11))))),
  (.branch 20 (.leaf (-5)) (.leaf (-4))),
  (.branch 25 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16))))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3372 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (7)) (.leaf (4)))))))
  code := certificateD8_3372
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-21))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 21 (.branch 18 (.branch 4 (.leaf (-21)) (.leaf (-20))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-16)) (.leaf (-14))))) (.branch 24 (.branch 22 (.leaf (-12)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 22 (.leaf (-12)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_241_3373 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (3)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 26 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3373
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-20)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-15))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.leaf (-2)),
  (.branch 23 (.branch 3 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 26 (.leaf (-7)) (.leaf (-5))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 23 (.branch 8 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 11 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))]
def witnessD8_241_3374 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (7)) (.leaf (3)))))))
  code := certificateD8_3374
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-4)) (.leaf (-2))),
  (.branch 23 (.branch 9 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2))]
def witnessD8_241_3375 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3375
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 24 (.branch 16 (.leaf (-21)) (.branch 23 (.leaf (-20)) (.leaf (-16)))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.branch 14 (.branch 7 (.leaf (-3)) (.leaf (-2))) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 19 (.branch 5 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 18 (.leaf (-10)) (.leaf (-9))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-7))) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_241_3376 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (6)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (2))) (.branch 26 (.leaf (4)) (.leaf (1)))))))
  code := certificateD8_3376
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 15 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 9 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17))))) (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_241_3377 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (6)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (7)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (5)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3377
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 22 (.leaf (-19)) (.leaf (-27)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-18)))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-27)) (.leaf (-23))) (.branch 25 (.leaf (-19)) (.branch 26 (.leaf (-15)) (.leaf (-11))))),
  (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 21 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 22 (.leaf (-15)) (.leaf (-13)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 26 (.leaf (-7)) (.leaf (-5))))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0))))]
def witnessD8_241_3378 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3378
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_241_3379 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_3379
  counts := ![(.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 24 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 16 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3380 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3380
  counts := ![(.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 24 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 16 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3381 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (6)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3381
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 22 (.branch 12 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3382 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (0)))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 24 (.leaf (7)) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD8_3382
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_241_3383 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (6)) (.leaf (0)))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_3383
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-9))))]
  high := ![(.branch 13 (.branch 3 (.leaf (-26)) (.branch 8 (.leaf (-25)) (.leaf (-24)))) (.branch 18 (.leaf (-23)) (.branch 23 (.leaf (-22)) (.leaf (-17))))),
  (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.leaf (-3)))))]
def witnessD8_241_3384 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_3384
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 18 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3385 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (7)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (4)))))))
  code := certificateD8_3385
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.leaf (-9)) (.leaf (-6))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3386 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3386
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3387 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3387
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 12 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-7)))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3388 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3388
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_241_3389 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (4)))))))
  code := certificateD8_3389
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 17 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_241_3390 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (2)))))))
  code := certificateD8_3390
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 20 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_241_3391 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (7)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (2)))))))
  code := certificateD8_3391
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-16))),
  (.branch 23 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-6)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3392 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3392
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3393 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3393
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 12 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-7)))),
  (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241_3394 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3394
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 22 (.leaf (-7)) (.leaf (-4))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_241_3395 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (7)) (.leaf (3)))))))
  code := certificateD8_3395
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.branch 23 (.leaf (-20)) (.leaf (-23))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 8 (.leaf (-13)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.leaf (-23)) (.branch 25 (.leaf (-16)) (.leaf (-9)))),
  (.branch 17 (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-8))))),
  (.branch 23 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_241_3396 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3396
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_241_3397 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (2)))))))
  code := certificateD8_3397
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-6)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 11 (.branch 5 (.branch 2 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 24 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-2)) (.leaf (0)))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_241_3398 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3398
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-4)) (.leaf (-2))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_241_3399 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3399
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_241_3400 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (7))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3400
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 24 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.branch 17 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_241_3401 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3401
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 17 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 11 (.branch 5 (.branch 2 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 17 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-9)))))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 15 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_241_3402 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6)))))))
  code := certificateD8_3402
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 25 (.leaf (-18)) (.leaf (-9))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.branch 12 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.leaf (-8)))) (.branch 23 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3))))))]
def witnessD8_241_3403 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6)))))))
  code := certificateD8_3403
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 11 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 25 (.leaf (-10)) (.leaf (-5))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_241_3404 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (7)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3404
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-5)) (.leaf (-4))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_241 : Fin 38 → CycleWitness 8 := ![witnessD8_241_3367, witnessD8_241_3368, witnessD8_241_3369, witnessD8_241_3370, witnessD8_241_3371, witnessD8_241_3372, witnessD8_241_3373, witnessD8_241_3374, witnessD8_241_3375, witnessD8_241_3376, witnessD8_241_3377, witnessD8_241_3378, witnessD8_241_3379, witnessD8_241_3380, witnessD8_241_3381, witnessD8_241_3382, witnessD8_241_3383, witnessD8_241_3384, witnessD8_241_3385, witnessD8_241_3386, witnessD8_241_3387, witnessD8_241_3388, witnessD8_241_3389, witnessD8_241_3390, witnessD8_241_3391, witnessD8_241_3392, witnessD8_241_3393, witnessD8_241_3394, witnessD8_241_3395, witnessD8_241_3396, witnessD8_241_3397, witnessD8_241_3398, witnessD8_241_3399, witnessD8_241_3400, witnessD8_241_3401, witnessD8_241_3402, witnessD8_241_3403, witnessD8_241_3404]
end RealPinwheel.FiveSixths


