-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_248
-- name    : RealPinwheel_FiveSixths_WitnessD8_248
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:30:49.533773+00:00
-- url     : https://prove2.me/theorems/e9c77405-2c70-4084-b7af-8c3beb3f8885
-- title:
--   Exact witness block D8_248
-- statement:
--   These exact witnesses represent words 3685 through 3725 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3685–3725; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_248_3684 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (7))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD8_3684
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-7)) (.leaf (-5))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_248_3685 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (7))))))
  code := certificateD8_3685
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3686 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (7))))))
  code := certificateD8_3686
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 5 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.branch 8 (.leaf (-11)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3687 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (7))) (.branch 15 (.leaf (0)) (.leaf (2))))))
  code := certificateD8_3687
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 2 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7)))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_248_3688 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (5))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3))))))
  code := certificateD8_3688
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 5 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 13 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_248_3689 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (2)) (.leaf (7))))))
  code := certificateD8_3689
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-12))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 10 (.leaf (-5)) (.leaf (-3))),
  (.branch 6 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_248_3690 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (7)) (.leaf (2))))))
  code := certificateD8_3690
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_248_3691 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (7)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2))))))
  code := certificateD8_3691
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 8 (.leaf (-11)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_248_3692 : CycleWitness 8 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (6)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (7)) (.leaf (2))))))
  code := certificateD8_3692
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_248_3693 : CycleWitness 8 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1))))))
  code := certificateD8_3693
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 4 (.leaf (-10)) (.branch 6 (.leaf (-11)) (.leaf (-12))))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 7 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-7)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3694 : CycleWitness 8 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (6)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (5))))))
  code := certificateD8_3694
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3695 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (4))))))
  code := certificateD8_3695
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 3 (.leaf (-11)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_248_3696 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (7)) (.leaf (4))))))
  code := certificateD8_3696
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_248_3697 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (2))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (6))) (.branch 14 (.leaf (2)) (.leaf (4))))))
  code := certificateD8_3697
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_248_3698 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (7))))))
  code := certificateD8_3698
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3699 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (7))))))
  code := certificateD8_3699
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3700 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (7))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (6))))))
  code := certificateD8_3700
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_248_3701 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (5))) (.branch 14 (.leaf (7)) (.leaf (3))))))
  code := certificateD8_3701
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.branch 5 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_248_3702 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2))))))
  code := certificateD8_3702
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 6 (.branch 2 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3703 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (7)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2))))))
  code := certificateD8_3703
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 6 (.branch 2 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_248_3704 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (7)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (4))))))
  code := certificateD8_3704
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_248_3705 : CycleWitness 8 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (4))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (7))))))
  code := certificateD8_3705
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3706 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (5))))))
  code := certificateD8_3706
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 4 (.leaf (-5)) (.branch 9 (.leaf (-4)) (.leaf (-3)))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3707 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (7))))))
  code := certificateD8_3707
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 5 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5))))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3708 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (7))))))
  code := certificateD8_3708
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3709 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (7)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4))))))
  code := certificateD8_3709
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 9 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3710 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (7)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4))))))
  code := certificateD8_3710
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-6)) (.leaf (-5))) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3711 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (7)) (.leaf (1))))))
  code := certificateD8_3711
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessD8_248_3712 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (4))))))
  code := certificateD8_3712
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_248_3713 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (2))) (.branch 13 (.leaf (5)) (.leaf (1))))))
  code := certificateD8_3713
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 8 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_248_3714 : CycleWitness 8 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (7))) (.branch 13 (.leaf (5)) (.leaf (2))))))
  code := certificateD8_3714
  counts := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_248_3715 : CycleWitness 8 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (7)) (.leaf (3))))))
  code := certificateD8_3715
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 4 (.leaf (-11)) (.branch 12 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_248_3716 : CycleWitness 8 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (7)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (4))))))
  code := certificateD8_3716
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 2 (.leaf (-7)) (.leaf (-6))),
  (.branch 7 (.branch 4 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 5 (.leaf (-9)) (.branch 6 (.leaf (-8)) (.leaf (-7))))) (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 6 (.leaf (-8)) (.branch 7 (.leaf (-7)) (.leaf (-6))))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_248_3717 : CycleWitness 8 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (7))) (.branch 12 (.leaf (5)) (.leaf (2))))))
  code := certificateD8_3717
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-9))) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.branch 7 (.leaf (-7)) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_248_3718 : CycleWitness 8 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (7))))))
  code := certificateD8_3718
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 2 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-4)) (.leaf (-3))),
  (.branch 10 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_248_3719 : CycleWitness 8 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (7)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (1))))))
  code := certificateD8_3719
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 8 (.leaf (-11)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 10 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 6 (.leaf (-8)) (.branch 7 (.leaf (-7)) (.leaf (-6))))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_248_3720 : CycleWitness 8 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (3)) (.leaf (1))))))
  code := certificateD8_3720
  counts := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-11)) (.branch 9 (.leaf (-10)) (.leaf (-8)))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 10 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_248_3721 : CycleWitness 8 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (7)) (.leaf (4))))))
  code := certificateD8_3721
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 6 (.leaf (-6)) (.branch 7 (.leaf (-5)) (.leaf (-4)))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 7 (.branch 5 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 6 (.leaf (-6)) (.leaf (-5)))) (.branch 9 (.branch 8 (.leaf (-4)) (.leaf (-3))) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.branch 7 (.leaf (-5)) (.leaf (-4))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_248_3722 : CycleWitness 8 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1))))))
  code := certificateD8_3722
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 5 (.leaf (-8)) (.branch 9 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 6 (.branch 4 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 6 (.branch 4 (.leaf (-7)) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3723 : CycleWitness 8 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (5))))))
  code := certificateD8_3723
  counts := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 7 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.branch 4 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 6 (.branch 4 (.leaf (-7)) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_248_3724 : CycleWitness 8 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (7)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5))))))
  code := certificateD8_3724
  counts := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-6))) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 5 (.branch 3 (.leaf (-7)) (.branch 4 (.leaf (-6)) (.leaf (-5)))) (.branch 7 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 6 (.branch 4 (.leaf (-6)) (.branch 5 (.leaf (-5)) (.leaf (-4)))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_248 : Fin 41 → CycleWitness 8 := ![witnessD8_248_3684, witnessD8_248_3685, witnessD8_248_3686, witnessD8_248_3687, witnessD8_248_3688, witnessD8_248_3689, witnessD8_248_3690, witnessD8_248_3691, witnessD8_248_3692, witnessD8_248_3693, witnessD8_248_3694, witnessD8_248_3695, witnessD8_248_3696, witnessD8_248_3697, witnessD8_248_3698, witnessD8_248_3699, witnessD8_248_3700, witnessD8_248_3701, witnessD8_248_3702, witnessD8_248_3703, witnessD8_248_3704, witnessD8_248_3705, witnessD8_248_3706, witnessD8_248_3707, witnessD8_248_3708, witnessD8_248_3709, witnessD8_248_3710, witnessD8_248_3711, witnessD8_248_3712, witnessD8_248_3713, witnessD8_248_3714, witnessD8_248_3715, witnessD8_248_3716, witnessD8_248_3717, witnessD8_248_3718, witnessD8_248_3719, witnessD8_248_3720, witnessD8_248_3721, witnessD8_248_3722, witnessD8_248_3723, witnessD8_248_3724]
end RealPinwheel.FiveSixths


