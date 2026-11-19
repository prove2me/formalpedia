-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_246
-- name    : RealPinwheel_FiveSixths_WitnessD8_246
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:27:57.109654+00:00
-- url     : https://prove2.me/theorems/b2e8ef13-bd4b-4309-a2b0-aa2f362a7059
-- title:
--   Exact witness block D8_246
-- statement:
--   These exact witnesses represent words 3577 through 3627 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3577–3627; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_246_3576 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3576
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 8 (.branch 2 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7))))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_246_3577 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (5)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3577
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_246_3578 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3578
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_246_3579 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_3579
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 3 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3580 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3580
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_246_3581 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (6)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (7)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (6)))))))
  code := certificateD8_3581
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3582 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3582
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_246_3583 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3583
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 17 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 7 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3584 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (4))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (7)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (5)))))))
  code := certificateD8_3584
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 17 (.branch 9 (.leaf (-6)) (.leaf (-5))) (.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3585 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (7)) (.leaf (5)))))))
  code := certificateD8_3585
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.leaf (-7)))) (.branch 18 (.branch 17 (.leaf (-6)) (.leaf (-5))) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1))]
def witnessD8_246_3586 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (7)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (6))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (2))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4)))))))
  code := certificateD8_3586
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 6 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 3 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3587 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3587
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_246_3588 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (7)) (.leaf (0))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3588
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 6 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3589 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (7)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4)))))))
  code := certificateD8_3589
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 13 (.branch 7 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 17 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3590 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (2)))))))
  code := certificateD8_3590
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 19 (.leaf (-14)) (.leaf (-7))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.leaf (-6)) (.leaf (-5))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3591 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (7)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (6)) (.leaf (3)))))))
  code := certificateD8_3591
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3592 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (7))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (7))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (2)) (.leaf (5)))))))
  code := certificateD8_3592
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 6 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3593 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3593
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3594 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (0))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3594
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_246_3595 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (6))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (4)))))))
  code := certificateD8_3595
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 6 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 3 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3596 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (5)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (5)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3596
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 6 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_246_3597 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3597
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 8 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_246_3598 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (7))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3598
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3599 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (7))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (4)) (.leaf (1)))))))
  code := certificateD8_3599
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 18 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 16 (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-4)) (.leaf (-3))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3600 : CycleWitness 8 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (7))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (2)))))))
  code := certificateD8_3600
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-18))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 6 (.branch 4 (.branch 3 (.leaf (-18)) (.leaf (-17))) (.branch 5 (.leaf (-16)) (.leaf (-15)))) (.branch 8 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3601 : CycleWitness 8 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (7)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5)))))))
  code := certificateD8_3601
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-10)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 8 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-10))))),
  (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-13)) (.branch 8 (.leaf (-12)) (.leaf (-11)))) (.branch 10 (.leaf (-10)) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3602 : CycleWitness 8 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (7))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_3602
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 3 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-13)) (.branch 8 (.leaf (-12)) (.leaf (-11)))) (.branch 10 (.leaf (-10)) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3603 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3603
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_246_3604 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (7)))))))
  code := certificateD8_3604
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-11)) (.leaf (-9))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_246_3605 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (6))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (2)))))))
  code := certificateD8_3605
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 11 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 15 (.branch 12 (.leaf (-18)) (.leaf (-16))) (.branch 18 (.leaf (-14)) (.leaf (-7)))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 6 (.leaf (-7)) (.leaf (-6))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3606 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (4)))))))
  code := certificateD8_3606
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 13 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-13)) (.branch 18 (.leaf (-10)) (.leaf (-6)))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-13)) (.branch 8 (.leaf (-12)) (.leaf (-11)))) (.branch 10 (.leaf (-10)) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_246_3607 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3607
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 5 (.leaf (-14)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-2)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-14)) (.branch 7 (.leaf (-13)) (.leaf (-12)))) (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-13)) (.branch 8 (.leaf (-12)) (.leaf (-11)))) (.branch 10 (.leaf (-10)) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_246_3608 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (7)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3608
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-4)) (.leaf (-6)))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 13 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-14)) (.branch 7 (.leaf (-13)) (.leaf (-12)))) (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3609 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (7))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (3)))))))
  code := certificateD8_3609
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3610 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (6))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3610
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 17 (.branch 16 (.leaf (-16)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 6 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (0)))),
  (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3611 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (7)))))))
  code := certificateD8_3611
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-15)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-10)) (.leaf (-5)))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 11 (.leaf (-8)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_246_3612 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (7)))))))
  code := certificateD8_3612
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 16 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3))))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_246_3613 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (7)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (5)) (.leaf (4)))))))
  code := certificateD8_3613
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-6)) (.leaf (-3))),
  (.branch 17 (.branch 10 (.leaf (-11)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-2)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3614 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (6)) (.leaf (2)))))))
  code := certificateD8_3614
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 16 (.leaf (-14)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-9)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 15 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-11)) (.leaf (-6)))),
  (.branch 14 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 18 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (0)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3615 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (4)) (.leaf (7))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (5)))))))
  code := certificateD8_3615
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 11 (.leaf (-1)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 13 (.branch 5 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-4)) (.leaf (-3))),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-14)) (.branch 7 (.leaf (-13)) (.leaf (-12)))) (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3616 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (7)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3616
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-4)) (.leaf (-6)))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 13 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.leaf (-2)) (.branch 15 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3617 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (3))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD8_3617
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3618 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (7))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD8_3618
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-6)) (.leaf (-8)))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-5)) (.leaf (-3))),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3619 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3619
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 14 (.leaf (-17)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3620 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3620
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 12 (.branch 2 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 9 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_246_3621 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (4)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (7)) (.leaf (1)))))))
  code := certificateD8_3621
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-8))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.branch 6 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.branch 5 (.leaf (-3)) (.leaf (-2))) (.branch 15 (.leaf (-1)) (.leaf (0)))),
  (.branch 8 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD8_246_3622 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (7)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (3))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (6)) (.leaf (1)))))))
  code := certificateD8_3622
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 16 (.branch 8 (.leaf (-17)) (.branch 15 (.leaf (-15)) (.leaf (-12)))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 5 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_246_3623 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (6)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3623
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.branch 10 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 11 (.leaf (-16)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.branch 3 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 15 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_246_3624 : CycleWitness 8 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (6)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (7)) (.leaf (1)))))))
  code := certificateD8_3624
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-15)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.leaf (-2)) (.branch 15 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-14))) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 18 (.leaf (-4)) (.leaf (-2))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1))]
def witnessD8_246_3625 : CycleWitness 8 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (6)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (7)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (0)) (.leaf (3))))))
  code := certificateD8_3625
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_246_3626 : CycleWitness 8 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (6))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3626
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_246 : Fin 51 → CycleWitness 8 := ![witnessD8_246_3576, witnessD8_246_3577, witnessD8_246_3578, witnessD8_246_3579, witnessD8_246_3580, witnessD8_246_3581, witnessD8_246_3582, witnessD8_246_3583, witnessD8_246_3584, witnessD8_246_3585, witnessD8_246_3586, witnessD8_246_3587, witnessD8_246_3588, witnessD8_246_3589, witnessD8_246_3590, witnessD8_246_3591, witnessD8_246_3592, witnessD8_246_3593, witnessD8_246_3594, witnessD8_246_3595, witnessD8_246_3596, witnessD8_246_3597, witnessD8_246_3598, witnessD8_246_3599, witnessD8_246_3600, witnessD8_246_3601, witnessD8_246_3602, witnessD8_246_3603, witnessD8_246_3604, witnessD8_246_3605, witnessD8_246_3606, witnessD8_246_3607, witnessD8_246_3608, witnessD8_246_3609, witnessD8_246_3610, witnessD8_246_3611, witnessD8_246_3612, witnessD8_246_3613, witnessD8_246_3614, witnessD8_246_3615, witnessD8_246_3616, witnessD8_246_3617, witnessD8_246_3618, witnessD8_246_3619, witnessD8_246_3620, witnessD8_246_3621, witnessD8_246_3622, witnessD8_246_3623, witnessD8_246_3624, witnessD8_246_3625, witnessD8_246_3626]
end RealPinwheel.FiveSixths


