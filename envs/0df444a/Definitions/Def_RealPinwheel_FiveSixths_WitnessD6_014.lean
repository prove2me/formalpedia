-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_014
-- name    : RealPinwheel_FiveSixths_WitnessD6_014
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:36.4032+00:00
-- url     : https://prove2.me/theorems/46c112c5-36d3-495f-b8c8-e402114016e6
-- title:
--   Exact witness block D6_014
-- statement:
--   These exact witnesses represent words 421 through 472 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 421–472; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_014_420 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_420
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_421 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_421
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_014_422 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_422
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 8 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_423 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_423
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_424 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_424
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-16)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 3 (.leaf (-3)) (.leaf (-2))) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 19 (.leaf (-10)) (.leaf (-9))))),
  (.leaf (-1))]
def witnessD6_014_425 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_425
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 17 (.leaf (-14)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-12)) (.leaf (-7)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_426 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_426
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_427 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_427
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-8)))),
  (.leaf (0))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 3 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD6_014_428 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5)))))))
  code := certificateD6_428
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0))]
def witnessD6_014_429 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_429
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-4)) (.leaf (-3))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_430 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_430
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-1)) (.leaf (0)))),
  (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_431 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_431
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 17 (.branch 9 (.leaf (-6)) (.leaf (-5))) (.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_432 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_432
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_433 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_433
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-14)))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_014_434 : CycleWitness 6 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_434
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_014_435 : CycleWitness 6 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_435
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-10)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-4)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 8 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-10))))),
  (.branch 9 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 16 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_014_436 : CycleWitness 6 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_436
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-11)) (.leaf (-22)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 9 (.branch 3 (.leaf (-22)) (.branch 6 (.leaf (-21)) (.leaf (-20)))) (.branch 15 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-11))))),
  (.branch 14 (.leaf (-5)) (.leaf (-4))),
  (.branch 17 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-2)) (.leaf (0))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-13)) (.branch 8 (.leaf (-12)) (.leaf (-11)))) (.branch 10 (.leaf (-10)) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_437 : CycleWitness 6 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_437
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 3 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-9)))),
  (.leaf (-2)),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_438 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_438
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-13)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.branch 6 (.leaf (-17)) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 15 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-8))))),
  (.branch 3 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (0)))),
  (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_014_439 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_439
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-11)))) (.branch 7 (.leaf (-12)) (.branch 9 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 10 (.leaf (-14)) (.leaf (-9))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 7 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_440 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_440
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 11 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-19)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-6)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 15 (.branch 12 (.leaf (-18)) (.leaf (-16))) (.branch 18 (.leaf (-14)) (.leaf (-7)))),
  (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-16))) (.branch 18 (.leaf (-13)) (.leaf (-10)))),
  (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 15 (.branch 13 (.leaf (-10)) (.branch 14 (.leaf (-9)) (.leaf (-8)))) (.branch 17 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (0))]
def witnessD6_014_441 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_441
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_442 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_442
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 11 (.leaf (-5)) (.leaf (-4))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.leaf (0))),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_443 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_443
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-12)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 15 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-14)) (.leaf (-7)))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 12 (.leaf (-5)) (.leaf (-3))),
  (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6)))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_444 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_444
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 9 (.leaf (-12)) (.branch 14 (.leaf (-10)) (.leaf (-8)))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_445 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_445
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-5)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 13 (.branch 10 (.leaf (-13)) (.leaf (-11))) (.branch 16 (.leaf (-9)) (.leaf (-7)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 9 (.leaf (-2)) (.branch 15 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_014_446 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_446
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 13 (.leaf (-13)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-11)) (.leaf (-6)))),
  (.branch 7 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5))))),
  (.branch 17 (.branch 10 (.leaf (-11)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_447 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_447
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.leaf (-17)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_448 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_448
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 13 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-13)) (.branch 18 (.leaf (-10)) (.leaf (-6)))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD6_014_449 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_449
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-10)) (.leaf (-5)))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.leaf (-8)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.branch 8 (.leaf (-4)) (.leaf (-3))) (.branch 10 (.leaf (-2)) (.branch 11 (.leaf (-1)) (.leaf (0))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_450 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (5))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_450
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.leaf (-2)) (.branch 15 (.leaf (-1)) (.leaf (0)))),
  (.branch 11 (.leaf (-8)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_451 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_451
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 16 (.branch 6 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-2)),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 5 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_452 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_452
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.branch 10 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.leaf (-16)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 12 (.leaf (-5)) (.leaf (-3))),
  (.branch 16 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014_453 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_453
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 16 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3))))),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD6_014_454 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_454
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-7))) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_455 : CycleWitness 6 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_455
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 13 (.branch 5 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 18 (.leaf (-6)) (.leaf (-3))),
  (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_456 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 14 (.branch 11 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_456
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 16 (.branch 14 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.leaf (12)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.leaf (-2)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_457 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_457
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 14 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 17 (.leaf (-4)) (.leaf (-2))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_014_458 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_458
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 14 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_014_459 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_459
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_014_460 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_460
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 4 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 14 (.leaf (-7)) (.leaf (-5))),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_014_461 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_461
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_462 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_462
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_014_463 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_463
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-11)) (.leaf (-22)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.branch 3 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-16)) (.leaf (-11)))),
  (.branch 4 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (0)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_014_464 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_464
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_465 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_465
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_014_466 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_466
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 7 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_467 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_467
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_014_468 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_468
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 10 (.branch 3 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-9)))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_014_469 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_469
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_014_470 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_470
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-7)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_014_471 : CycleWitness 6 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_471
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 15 (.leaf (-7)) (.leaf (-4))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_014 : Fin 52 → CycleWitness 6 := ![witnessD6_014_420, witnessD6_014_421, witnessD6_014_422, witnessD6_014_423, witnessD6_014_424, witnessD6_014_425, witnessD6_014_426, witnessD6_014_427, witnessD6_014_428, witnessD6_014_429, witnessD6_014_430, witnessD6_014_431, witnessD6_014_432, witnessD6_014_433, witnessD6_014_434, witnessD6_014_435, witnessD6_014_436, witnessD6_014_437, witnessD6_014_438, witnessD6_014_439, witnessD6_014_440, witnessD6_014_441, witnessD6_014_442, witnessD6_014_443, witnessD6_014_444, witnessD6_014_445, witnessD6_014_446, witnessD6_014_447, witnessD6_014_448, witnessD6_014_449, witnessD6_014_450, witnessD6_014_451, witnessD6_014_452, witnessD6_014_453, witnessD6_014_454, witnessD6_014_455, witnessD6_014_456, witnessD6_014_457, witnessD6_014_458, witnessD6_014_459, witnessD6_014_460, witnessD6_014_461, witnessD6_014_462, witnessD6_014_463, witnessD6_014_464, witnessD6_014_465, witnessD6_014_466, witnessD6_014_467, witnessD6_014_468, witnessD6_014_469, witnessD6_014_470, witnessD6_014_471]
end RealPinwheel.FiveSixths


