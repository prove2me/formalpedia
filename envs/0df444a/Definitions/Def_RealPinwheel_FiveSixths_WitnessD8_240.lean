-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_240
-- name    : RealPinwheel_FiveSixths_WitnessD8_240
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:23:00.773217+00:00
-- url     : https://prove2.me/theorems/c7cf1816-fe82-4f13-b03b-a4ed84a38f28
-- title:
--   Exact witness block D8_240
-- statement:
--   These exact witnesses represent words 3332 through 3367 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3332–3367; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_240_3331 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (7)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (6)) (.leaf (2)))))))
  code := certificateD8_3331
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 27 (.leaf (-6)) (.leaf (-5))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 26 (.branch 16 (.leaf (-11)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3332 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (4)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3332
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-21)))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-16)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0))]
  high := ![(.branch 21 (.branch 11 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 13 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-11)) (.leaf (-7))))),
  (.leaf (-1)),
  (.branch 12 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 14 (.leaf (-17)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_240_3333 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (6)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (6))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3333
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 26 (.branch 21 (.leaf (-18)) (.leaf (-16))) (.branch 27 (.leaf (-13)) (.leaf (-10)))),
  (.leaf (-5)),
  (.branch 25 (.branch 16 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 25 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-9)))) (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_240_3334 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (7))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3334
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 27 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-18)) (.leaf (-16))) (.branch 27 (.leaf (-13)) (.leaf (-10)))),
  (.leaf (-5)),
  (.branch 25 (.branch 16 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-2)) (.leaf (0))),
  (.branch 25 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-9)))) (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 10 (.leaf (-19)) (.branch 11 (.leaf (-18)) (.leaf (-17))))) (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3335 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (2)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (6)) (.leaf (7)))))))
  code := certificateD8_3335
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 27 (.leaf (0)) (.leaf (-1))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.leaf (0))]
def witnessD8_240_3336 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (7)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3336
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-11)) (.leaf (-13)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 25 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 23 (.leaf (-13)) (.branch 24 (.leaf (-11)) (.leaf (-9)))) (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3))))),
  (.branch 9 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (0)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 9 (.leaf (-20)) (.branch 10 (.leaf (-19)) (.leaf (-18))))) (.branch 14 (.branch 12 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7))))) (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3337 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3337
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 15 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 19 (.leaf (-16)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-10)) (.leaf (-6))))),
  (.branch 27 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-5)) (.leaf (-3)))),
  (.branch 23 (.branch 21 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-3)) (.leaf (-2))) (.branch 15 (.leaf (-1)) (.leaf (0))))]
def witnessD8_240_3338 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3338
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-19))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_240_3339 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (7)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (6))) (.branch 27 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3339
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-23)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.branch 13 (.leaf (-24)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7)))),
  (.branch 18 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-10)) (.leaf (-7))))),
  (.branch 24 (.branch 4 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 5 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-12)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-6)) (.branch 27 (.leaf (-5)) (.leaf (-3)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3340 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (5)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (7)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3340
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 25 (.branch 2 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3341 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (7)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (6)))))))
  code := certificateD8_3341
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-23)) (.leaf (-24)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.branch 13 (.leaf (-24)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.leaf (-10)) (.leaf (-5))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 4 (.leaf (-19)) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3342 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (7)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (3))) (.branch 27 (.leaf (1)) (.leaf (6)))))))
  code := certificateD8_3342
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.branch 2 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3343 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (4))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (7)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (4))) (.branch 27 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_3343
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-20))),
  (.branch 22 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 19 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-20)) (.leaf (-19))) (.branch 11 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16))))) (.branch 15 (.branch 14 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-13)) (.branch 17 (.leaf (-12)) (.leaf (-11)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3344 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (7)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (6))) (.branch 20 (.leaf (2)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3344
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-22))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-6)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 22 (.branch 3 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-18)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-9))) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-8)) (.branch 27 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_240_3345 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3345
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_240_3346 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (6)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3346
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 25 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_240_3347 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (7))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (7))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (6)))))))
  code := certificateD8_3347
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 17 (.leaf (-26)) (.leaf (-27)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-18))) (.branch 24 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 25 (.branch 18 (.leaf (-27)) (.branch 24 (.leaf (-25)) (.leaf (-20)))) (.branch 26 (.leaf (-15)) (.branch 27 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-15))) (.branch 27 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-6))))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3348 : CycleWitness 8 where
  length := 28
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3348
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 23 (.leaf (-14)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-16))),
  (.branch 26 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 27 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 26 (.leaf (-3)) (.branch 27 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-12))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-6)) (.leaf (-3))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 26 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 27 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_240_3349 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 17 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (0))) (.branch 26 (.leaf (7)) (.leaf (1)))))))
  code := certificateD8_3349
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 17 (.leaf (-16)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-11)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-15))),
  (.branch 26 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.leaf (-20)) (.branch 26 (.leaf (-18)) (.leaf (-13)))),
  (.branch 12 (.branch 4 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.branch 16 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0))))),
  (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-13)) (.leaf (-11)))) (.branch 25 (.leaf (-9)) (.branch 26 (.leaf (-7)) (.leaf (-5))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-18)) (.leaf (-17))) (.branch 12 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.branch 14 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-15)) (.branch 14 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 18 (.leaf (-10)) (.leaf (-9))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-7))) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_240_3350 : CycleWitness 8 where
  length := 27
  word := (.branch 14 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3350
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 20 (.branch 17 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 19 (.leaf (9)) (.leaf (10)))) (.branch 24 (.branch 22 (.leaf (11)) (.leaf (12))) (.branch 26 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-15)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 24 (.branch 10 (.leaf (-18)) (.branch 17 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 9 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17))))) (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3351 : CycleWitness 8 where
  length := 27
  word := (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3351
  counts := ![(.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 24 (.branch 22 (.leaf (12)) (.leaf (13))) (.branch 26 (.leaf (14)) (.leaf (15)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-21)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-20))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-16)) (.leaf (-14))))) (.branch 24 (.branch 22 (.leaf (-12)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 23 (.branch 8 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.leaf (-4)) (.leaf (-2))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-18)) (.leaf (-17))) (.branch 12 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.branch 14 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3352 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3352
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 21 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-19)) (.leaf (-22)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-16))),
  (.branch 24 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 26 (.leaf (-8)) (.leaf (-4))),
  (.branch 23 (.branch 9 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 23 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 19 (.branch 15 (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-11))) (.branch 18 (.leaf (-10)) (.leaf (-9))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-7))) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_240_3353 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (1)) (.leaf (3))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3353
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 24 (.leaf (-11)) (.leaf (-18)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 15 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-17))),
  (.branch 23 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 23 (.leaf (-11)) (.branch 26 (.leaf (-10)) (.leaf (-6))))),
  (.branch 25 (.leaf (-18)) (.branch 26 (.leaf (-14)) (.leaf (-10)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 15 (.branch 9 (.branch 6 (.branch 5 (.leaf (-23)) (.leaf (-22))) (.branch 7 (.leaf (-21)) (.branch 8 (.leaf (-20)) (.leaf (-19))))) (.branch 12 (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.leaf (-15)) (.branch 14 (.leaf (-14)) (.leaf (-13)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 13 (.leaf (-15)) (.leaf (-14)))) (.branch 16 (.branch 15 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-11)) (.leaf (-10))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_240_3354 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3354
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 17 (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))) (.branch 18 (.leaf (-10)) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3355 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (3))) (.branch 19 (.leaf (7)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3355
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-20)) (.leaf (-26)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-21))),
  (.branch 19 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 17 (.branch 9 (.branch 5 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 25 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.branch 26 (.leaf (-5)) (.leaf (-4))),
  (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-2)),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-21)) (.leaf (-20))) (.branch 9 (.leaf (-19)) (.branch 10 (.leaf (-18)) (.leaf (-17))))) (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-7))) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3356 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (3)))))))
  code := certificateD8_3356
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 21 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-19)) (.leaf (-18))) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_240_3357 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (5))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3357
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 18 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-10)) (.leaf (-8)))),
  (.branch 19 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 25 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 21 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3358 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (2)) (.leaf (4))) (.branch 19 (.leaf (0)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3358
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 19 (.branch 5 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 16 (.branch 14 (.leaf (-14)) (.branch 15 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3359 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (7)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (6)) (.leaf (3)))))))
  code := certificateD8_3359
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-20)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16))))]
  high := ![(.branch 25 (.leaf (-21)) (.branch 26 (.leaf (-14)) (.leaf (-7)))),
  (.branch 21 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 5 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_240_3360 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (5)))))))
  code := certificateD8_3360
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-22)) (.leaf (-24)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 16 (.leaf (-8)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-20))),
  (.branch 21 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 24 (.branch 7 (.leaf (-24)) (.branch 18 (.leaf (-23)) (.leaf (-20)))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-10)) (.leaf (-5))))),
  (.branch 20 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 17 (.leaf (-13)) (.leaf (-12))) (.branch 26 (.leaf (-10)) (.leaf (-8)))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16))))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3361 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (7))) (.branch 19 (.leaf (5)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (3)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (3)))))))
  code := certificateD8_3361
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-15)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 18 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 14 (.branch 6 (.branch 2 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 18 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))) (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.leaf (-2))))),
  (.branch 15 (.branch 9 (.branch 6 (.branch 5 (.leaf (-23)) (.leaf (-22))) (.branch 7 (.leaf (-21)) (.branch 8 (.leaf (-20)) (.leaf (-19))))) (.branch 12 (.branch 10 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.leaf (-15)) (.branch 14 (.leaf (-14)) (.leaf (-13)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))) (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-8)) (.leaf (-7))))) (.branch 24 (.branch 22 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_240_3362 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (2)) (.branch 22 (.leaf (5)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3362
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-17)) (.leaf (-19)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-1)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 19 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-3)),
  (.branch 24 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 9 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 17 (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))) (.branch 18 (.leaf (-10)) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3363 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (4)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3363
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-20)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-18))),
  (.branch 23 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 25 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-17)) (.leaf (-10)))),
  (.branch 11 (.branch 3 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 19 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.leaf (-7))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 21 (.leaf (-17)) (.branch 22 (.leaf (-15)) (.leaf (-13)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 26 (.leaf (-7)) (.leaf (-5))))),
  (.branch 22 (.branch 20 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 21 (.leaf (-14)) (.leaf (-12)))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-18)) (.leaf (-17))) (.branch 12 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.branch 14 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-11)) (.leaf (-10)))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_240_3364 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (5)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3364
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 26 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-2)),
  (.branch 24 (.branch 13 (.leaf (-6)) (.branch 23 (.leaf (-5)) (.leaf (-4)))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 12 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-14))) (.branch 22 (.leaf (-12)) (.leaf (-10)))) (.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 17 (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))) (.branch 18 (.leaf (-10)) (.branch 19 (.leaf (-9)) (.leaf (-8))))) (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 26 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_240_3365 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (7)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (4)))))))
  code := certificateD8_3365
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 22 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 3 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-19)) (.leaf (-18))) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 14 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 15 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-11)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6))))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.branch 26 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_240_3366 : CycleWitness 8 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (5)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (6)) (.leaf (2)))))))
  code := certificateD8_3366
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 12 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-19)) (.leaf (-20)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 20 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 13 (.leaf (-21)) (.leaf (-20))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6)))),
  (.branch 22 (.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 24 (.branch 9 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-8)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 24 (.branch 22 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5)))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))))]
def witnessD8_240 : Fin 36 → CycleWitness 8 := ![witnessD8_240_3331, witnessD8_240_3332, witnessD8_240_3333, witnessD8_240_3334, witnessD8_240_3335, witnessD8_240_3336, witnessD8_240_3337, witnessD8_240_3338, witnessD8_240_3339, witnessD8_240_3340, witnessD8_240_3341, witnessD8_240_3342, witnessD8_240_3343, witnessD8_240_3344, witnessD8_240_3345, witnessD8_240_3346, witnessD8_240_3347, witnessD8_240_3348, witnessD8_240_3349, witnessD8_240_3350, witnessD8_240_3351, witnessD8_240_3352, witnessD8_240_3353, witnessD8_240_3354, witnessD8_240_3355, witnessD8_240_3356, witnessD8_240_3357, witnessD8_240_3358, witnessD8_240_3359, witnessD8_240_3360, witnessD8_240_3361, witnessD8_240_3362, witnessD8_240_3363, witnessD8_240_3364, witnessD8_240_3365, witnessD8_240_3366]
end RealPinwheel.FiveSixths


