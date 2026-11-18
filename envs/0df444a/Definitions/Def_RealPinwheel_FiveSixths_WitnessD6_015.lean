-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_015
-- name    : RealPinwheel_FiveSixths_WitnessD6_015
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:29.0272+00:00
-- url     : https://prove2.me/theorems/c5619642-d699-4322-a9d8-47e409877cbc
-- title:
--   Exact witness block D6_015
-- statement:
--   These exact witnesses represent words 473 through 529 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 473–529; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_015_472 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_472
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-6)) (.leaf (-4))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_015_473 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (3)))))))
  code := certificateD6_473
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 8 (.leaf (-15)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 9 (.leaf (-16)) (.branch 17 (.leaf (-14)) (.leaf (-7)))),
  (.branch 16 (.leaf (-11)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_474 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_474
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 17 (.leaf (-8)) (.leaf (-4))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_015_475 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_475
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 15 (.leaf (-7)) (.leaf (-4))),
  (.branch 16 (.branch 3 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_476 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_476
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 3 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 15 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_477 : CycleWitness 6 where
  length := 18
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_477
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 6 (.leaf (-11)) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_015_478 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_478
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_479 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_479
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 5 (.leaf (-1)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 16 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 15 (.branch 10 (.leaf (-3)) (.leaf (-2))) (.branch 16 (.leaf (-1)) (.leaf (0)))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_015_480 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_480
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 16 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 8 (.leaf (-3)) (.leaf (-2))) (.branch 10 (.leaf (-1)) (.leaf (0)))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_481 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_481
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_482 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_482
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_483 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_483
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_484 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_484
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 16 (.branch 12 (.leaf (-17)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 17 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_485 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_485
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.leaf (-10)) (.leaf (-5))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_486 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_486
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_487 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_487
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 4 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 16 (.branch 5 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_488 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_488
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 7 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-7)))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.leaf (-3)) (.leaf (0))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-15)) (.branch 5 (.leaf (-14)) (.leaf (-13)))) (.branch 8 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 9 (.leaf (-10)) (.leaf (-9))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_489 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_489
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD6_015_490 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_490
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 16 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 10 (.leaf (-5)) (.leaf (-4))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_491 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_491
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 13 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_492 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_492
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-7)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_493 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_493
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 7 (.leaf (-6)) (.leaf (-5))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 4 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_494 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_494
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 7 (.leaf (-10)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 16 (.leaf (-10)) (.branch 17 (.leaf (-7)) (.leaf (-4))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_015_495 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_495
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 13 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-5)),
  (.leaf (0)),
  (.branch 15 (.branch 4 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_496 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_496
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 13 (.branch 2 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 4 (.leaf (-2)) (.branch 8 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_497 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_497
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_498 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_498
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 16 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-15)) (.branch 15 (.leaf (-13)) (.leaf (-10)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_015_499 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_499
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 5 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_015_500 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_500
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 3 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-8)))),
  (.branch 7 (.leaf (-2)) (.branch 11 (.leaf (-1)) (.leaf (0)))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_015_501 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_501
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-5)),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.leaf (-4)) (.leaf (-2))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_015_502 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_502
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-11)) (.leaf (-22)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 11 (.branch 3 (.leaf (-22)) (.branch 7 (.leaf (-21)) (.leaf (-20)))) (.branch 15 (.leaf (-19)) (.branch 16 (.leaf (-15)) (.leaf (-11))))),
  (.branch 4 (.leaf (-5)) (.leaf (-4))),
  (.branch 10 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_503 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_503
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_015_504 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2))))))
  code := certificateD6_504
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 8 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.leaf (-4))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_505 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.leaf (2))))))
  code := certificateD6_505
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.branch 15 (.leaf (-1)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 9 (.branch 5 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-2)) (.branch 9 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.leaf (-5)) (.leaf (-4))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_506 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_506
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 4 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 5 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-8)))),
  (.branch 11 (.leaf (-4)) (.leaf (-3))),
  (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_507 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (1))))))
  code := certificateD6_507
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_508 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_508
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.leaf (-7)))),
  (.branch 10 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-11)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_015_509 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_509
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_510 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_510
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 7 (.leaf (-11)) (.branch 9 (.leaf (-12)) (.leaf (-13))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 10 (.leaf (-13)) (.leaf (-8))),
  (.branch 11 (.leaf (-11)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_511 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_511
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 6 (.leaf (-11)) (.leaf (-8))),
  (.branch 14 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_512 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_512
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.branch 14 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.branch 5 (.leaf (-5)) (.branch 11 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_513 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_513
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 9 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-7)))),
  (.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.leaf (-4)) (.leaf (-2))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_514 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_514
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 12 (.leaf (-14)) (.leaf (-8))),
  (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-12)) (.leaf (-10)))) (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 7 (.leaf (-5)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_515 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_515
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.branch 7 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 5 (.leaf (-7)) (.leaf (-6))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_516 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_516
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.branch 3 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-4)))),
  (.branch 9 (.leaf (-2)) (.leaf (0))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_517 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_517
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.branch 3 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-4)))),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_518 : CycleWitness 6 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_518
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 8 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 12 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-11))))),
  (.branch 11 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_519 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_519
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 8 (.leaf (-9)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 8 (.branch 2 (.leaf (-11)) (.branch 5 (.leaf (-10)) (.leaf (-9)))) (.branch 11 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))),
  (.branch 9 (.leaf (-11)) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_015_520 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_520
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 8 (.branch 2 (.leaf (-11)) (.branch 5 (.leaf (-10)) (.leaf (-9)))) (.branch 11 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))),
  (.branch 7 (.leaf (-10)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_521 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_521
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 6 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_522 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_522
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 11 (.leaf (-11)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_523 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_523
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (0)))),
  (.branch 8 (.leaf (-6)) (.leaf (-4))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_015_524 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_524
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 4 (.leaf (-5)) (.leaf (-4))),
  (.branch 5 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_015_525 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (4)) (.leaf (3)))))))
  code := certificateD6_525
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 11 (.leaf (-11)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_015_526 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_526
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-13)) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD6_015_527 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (3)))))))
  code := certificateD6_527
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 15 (.branch 6 (.leaf (-14)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_015_528 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_528
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-5)))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0))))),
  (.branch 14 (.branch 4 (.leaf (-6)) (.leaf (-5))) (.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2))))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_015 : Fin 57 → CycleWitness 6 := ![witnessD6_015_472, witnessD6_015_473, witnessD6_015_474, witnessD6_015_475, witnessD6_015_476, witnessD6_015_477, witnessD6_015_478, witnessD6_015_479, witnessD6_015_480, witnessD6_015_481, witnessD6_015_482, witnessD6_015_483, witnessD6_015_484, witnessD6_015_485, witnessD6_015_486, witnessD6_015_487, witnessD6_015_488, witnessD6_015_489, witnessD6_015_490, witnessD6_015_491, witnessD6_015_492, witnessD6_015_493, witnessD6_015_494, witnessD6_015_495, witnessD6_015_496, witnessD6_015_497, witnessD6_015_498, witnessD6_015_499, witnessD6_015_500, witnessD6_015_501, witnessD6_015_502, witnessD6_015_503, witnessD6_015_504, witnessD6_015_505, witnessD6_015_506, witnessD6_015_507, witnessD6_015_508, witnessD6_015_509, witnessD6_015_510, witnessD6_015_511, witnessD6_015_512, witnessD6_015_513, witnessD6_015_514, witnessD6_015_515, witnessD6_015_516, witnessD6_015_517, witnessD6_015_518, witnessD6_015_519, witnessD6_015_520, witnessD6_015_521, witnessD6_015_522, witnessD6_015_523, witnessD6_015_524, witnessD6_015_525, witnessD6_015_526, witnessD6_015_527, witnessD6_015_528]
end RealPinwheel.FiveSixths


