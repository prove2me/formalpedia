-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_242
-- name    : RealPinwheel_FiveSixths_WitnessD8_242
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:25:34.941721+00:00
-- url     : https://prove2.me/theorems/a72c9cca-0a4f-4b13-aa60-cbbea05e1acf
-- title:
--   Exact witness block D8_242
-- statement:
--   These exact witnesses represent words 3406 through 3443 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3406–3443; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_242_3405 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3405
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3406 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3406
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3407 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3407
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-5)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3408 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3408
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3409 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3409
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 18 (.leaf (-19)) (.branch 25 (.leaf (-16)) (.leaf (-9)))),
  (.branch 3 (.leaf (-9)) (.leaf (-8))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 24 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3410 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3410
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 13 (.leaf (-12)) (.branch 18 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 17 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))),
  (.branch 19 (.leaf (-14)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 9 (.branch 6 (.branch 5 (.leaf (-22)) (.leaf (-21))) (.branch 7 (.leaf (-20)) (.branch 8 (.leaf (-19)) (.leaf (-18))))) (.branch 12 (.branch 10 (.leaf (-17)) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_242_3411 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (7)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (4)) (.leaf (6)))))))
  code := certificateD8_3411
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-14)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 24 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.branch 12 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.branch 23 (.branch 13 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3412 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3412
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-20)) (.leaf (-22)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 22 (.branch 20 (.branch 11 (.leaf (-22)) (.leaf (-21))) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 12 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3413 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (7)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (6)))))))
  code := certificateD8_3413
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 15 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 18 (.leaf (-19)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 5 (.leaf (-6)) (.leaf (-5))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3414 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3414
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 18 (.leaf (-19)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 5 (.leaf (-6)) (.leaf (-5))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3415 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (7)))))))
  code := certificateD8_3415
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 15 (.leaf (-16)) (.leaf (-20)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.branch 25 (.leaf (-13)) (.leaf (-8))))),
  (.branch 23 (.branch 15 (.leaf (-11)) (.branch 22 (.leaf (-10)) (.leaf (-8)))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 5 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-11))) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 22 (.branch 7 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3416 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (5)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3416
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 22 (.branch 4 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_242_3417 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3417
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3418 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (3)) (.leaf (2)))))))
  code := certificateD8_3418
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 23 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-4))))),
  (.branch 24 (.branch 8 (.leaf (-17)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-4)) (.leaf (0))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 22 (.branch 4 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3419 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (7)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (2)) (.leaf (5)))))))
  code := certificateD8_3419
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-7)) (.leaf (-5))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 20 (.leaf (-8)) (.branch 21 (.leaf (-7)) (.leaf (-6)))) (.branch 24 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3420 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (4)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (5)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (6))) (.branch 25 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3420
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3421 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (7)) (.leaf (3)))))))
  code := certificateD8_3421
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_242_3422 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3422
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-7)) (.leaf (-5))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3423 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3423
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 23 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 14 (.branch 8 (.branch 5 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 6 (.leaf (-21)) (.branch 7 (.leaf (-20)) (.leaf (-19))))) (.branch 11 (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3424 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_3424
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 22 (.branch 12 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 5 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_242_3425 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_3425
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-20)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 22 (.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3426 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (3)) (.leaf (4)))))))
  code := certificateD8_3426
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 15 (.leaf (-16)) (.leaf (-20)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.branch 25 (.leaf (-13)) (.leaf (-8))))),
  (.branch 23 (.branch 15 (.leaf (-11)) (.branch 22 (.leaf (-10)) (.leaf (-8)))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 5 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 22 (.branch 7 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 18 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3427 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (1)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (7))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_3427
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 12 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.branch 5 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3428 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3428
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-5)) (.leaf (-3))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 9 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_242_3429 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (3)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (7)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3429
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (-21)) (.leaf (-22)))) (.branch 16 (.leaf (-23)) (.branch 21 (.leaf (-24)) (.leaf (-25))))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 23 (.branch 22 (.leaf (-25)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 9 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 18 (.leaf (-16)) (.leaf (-13))) (.branch 25 (.leaf (-9)) (.leaf (-5)))),
  (.branch 5 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_242_3430 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (7)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (4)))))))
  code := certificateD8_3430
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-23)) (.leaf (-24))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 23 (.branch 17 (.leaf (-24)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 4 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3431 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (7)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (6)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (7)) (.leaf (5)))))))
  code := certificateD8_3431
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-23)) (.leaf (-24))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.branch 17 (.leaf (-24)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 4 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_242_3432 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3432
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-22))),
  (.branch 17 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-5)) (.leaf (-3))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 9 (.branch 6 (.branch 5 (.leaf (-22)) (.leaf (-21))) (.branch 7 (.leaf (-20)) (.branch 8 (.leaf (-19)) (.leaf (-18))))) (.branch 12 (.branch 10 (.leaf (-17)) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3433 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (1)))))))
  code := certificateD8_3433
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-21))),
  (.branch 18 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.branch 4 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-21)) (.leaf (-20))) (.branch 8 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17))))) (.branch 12 (.branch 11 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3434 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (7)) (.leaf (1)))))))
  code := certificateD8_3434
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-19))),
  (.branch 20 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-14))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.leaf (-2)) (.leaf (0))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 11 (.branch 9 (.branch 8 (.leaf (-19)) (.leaf (-18))) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_242_3435 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (5)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (4)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (7)))))))
  code := certificateD8_3435
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 12 (.leaf (-23)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-10)) (.leaf (-5))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3)))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3436 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (6)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (7)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (3)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3436
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-21)) (.leaf (-22)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 14 (.leaf (-7)) (.branch 19 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.branch 7 (.leaf (-22)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 20 (.leaf (-9)) (.leaf (-5))),
  (.branch 22 (.branch 12 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 24 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 25 (.leaf (-3)) (.leaf (-2)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3437 : CycleWitness 8 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (5)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (4)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (2)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3437
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-10)) (.leaf (-8)))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-4)) (.leaf (-2))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3438 : CycleWitness 8 where
  length := 25
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (7)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (3)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))))))
  code := certificateD8_3438
  counts := ![(.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 24 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-22))),
  (.branch 16 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 20 (.leaf (-5)) (.branch 24 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.branch 24 (.leaf (-5)) (.leaf (-3))))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-17)) (.leaf (-16))) (.branch 11 (.leaf (-15)) (.leaf (-14)))) (.branch 14 (.branch 13 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-11)) (.leaf (-10))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-7)) (.leaf (-6)))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 8 (.branch 5 (.branch 4 (.leaf (-22)) (.leaf (-21))) (.branch 6 (.leaf (-20)) (.branch 7 (.leaf (-19)) (.leaf (-18))))) (.branch 11 (.branch 9 (.leaf (-17)) (.branch 10 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.leaf (-14)) (.branch 13 (.leaf (-13)) (.leaf (-12)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-7)) (.leaf (-6)))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_242_3439 : CycleWitness 8 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3439
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-16))),
  (.branch 22 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))),
  (.branch 16 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 20 (.leaf (-19)) (.branch 24 (.leaf (-18)) (.leaf (-13))))),
  (.branch 22 (.branch 4 (.leaf (-16)) (.branch 21 (.leaf (-15)) (.leaf (-12)))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-16)) (.leaf (-14))) (.branch 20 (.leaf (-12)) (.leaf (-10)))) (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-6))) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-16)) (.leaf (-15))) (.branch 12 (.leaf (-14)) (.leaf (-13)))) (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-11))) (.branch 16 (.leaf (-10)) (.leaf (-9))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-7))) (.branch 20 (.leaf (-6)) (.leaf (-5)))) (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3440 : CycleWitness 8 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (2)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3440
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-20))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 10 (.leaf (-12)) (.branch 18 (.leaf (-13)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 18 (.leaf (-20)) (.leaf (-16))) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 19 (.leaf (-15)) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 22 (.branch 12 (.leaf (-17)) (.branch 21 (.leaf (-15)) (.leaf (-12)))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 22 (.branch 13 (.leaf (-14)) (.leaf (-12))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 20 (.leaf (-12)) (.branch 21 (.leaf (-10)) (.leaf (-8)))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-11)) (.leaf (-10)))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_242_3441 : CycleWitness 8 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (5)) (.leaf (7))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (5)))))))
  code := certificateD8_3441
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-15)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-18)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-19))),
  (.branch 18 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-15)) (.leaf (-13))) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 22 (.branch 15 (.leaf (-19)) (.leaf (-16))) (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-8)) (.leaf (-4))))),
  (.branch 22 (.branch 12 (.leaf (-17)) (.branch 21 (.leaf (-15)) (.leaf (-12)))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-4)) (.leaf (-3))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.branch 24 (.leaf (-5)) (.leaf (-3))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-19)) (.leaf (-18))) (.branch 9 (.leaf (-17)) (.leaf (-16)))) (.branch 12 (.branch 11 (.leaf (-15)) (.leaf (-14))) (.branch 13 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-11)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-7)) (.branch 20 (.leaf (-6)) (.leaf (-5)))) (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242_3442 : CycleWitness 8 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (7)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3442
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 17 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 23 (.branch 14 (.leaf (-19)) (.leaf (-16))) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 20 (.leaf (-8)) (.leaf (-6))),
  (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-12))) (.branch 24 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.leaf (-8)) (.branch 24 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-8))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 9 (.branch 6 (.branch 5 (.leaf (-21)) (.leaf (-20))) (.branch 7 (.leaf (-19)) (.branch 8 (.leaf (-18)) (.leaf (-17))))) (.branch 11 (.branch 10 (.leaf (-16)) (.leaf (-15))) (.branch 12 (.leaf (-14)) (.branch 13 (.leaf (-13)) (.leaf (-12)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-7))) (.branch 20 (.leaf (-6)) (.leaf (-5)))) (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_242 : Fin 38 → CycleWitness 8 := ![witnessD8_242_3405, witnessD8_242_3406, witnessD8_242_3407, witnessD8_242_3408, witnessD8_242_3409, witnessD8_242_3410, witnessD8_242_3411, witnessD8_242_3412, witnessD8_242_3413, witnessD8_242_3414, witnessD8_242_3415, witnessD8_242_3416, witnessD8_242_3417, witnessD8_242_3418, witnessD8_242_3419, witnessD8_242_3420, witnessD8_242_3421, witnessD8_242_3422, witnessD8_242_3423, witnessD8_242_3424, witnessD8_242_3425, witnessD8_242_3426, witnessD8_242_3427, witnessD8_242_3428, witnessD8_242_3429, witnessD8_242_3430, witnessD8_242_3431, witnessD8_242_3432, witnessD8_242_3433, witnessD8_242_3434, witnessD8_242_3435, witnessD8_242_3436, witnessD8_242_3437, witnessD8_242_3438, witnessD8_242_3439, witnessD8_242_3440, witnessD8_242_3441, witnessD8_242_3442]
end RealPinwheel.FiveSixths


