-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_012
-- name    : RealPinwheel_FiveSixths_WitnessD6_012
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:53.058411+00:00
-- url     : https://prove2.me/theorems/ef3f2548-84d2-415b-b1a1-247fc6785765
-- title:
--   Exact witness block D6_012
-- statement:
--   These exact witnesses represent words 330 through 372 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 330–372; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_012_329 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_329
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_330 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_330
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_331 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_331
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 17 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-3)))) (.branch 20 (.leaf (-2)) (.branch 21 (.leaf (-1)) (.leaf (0))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-17)) (.leaf (-16))) (.branch 10 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-10))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_332 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_332
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.branch 21 (.leaf (-13)) (.leaf (-9))))),
  (.branch 17 (.branch 7 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7)))) (.branch 22 (.branch 21 (.leaf (-6)) (.leaf (-5))) (.branch 23 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD6_012_333 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_333
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_012_334 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_334
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_012_335 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_335
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-11))))]
  high := ![(.branch 9 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.branch 19 (.leaf (-10)) (.leaf (-9))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8)))) (.branch 21 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 22 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3))))))]
def witnessD6_012_336 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_336
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD6_012_337 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_337
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_338 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_338
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_339 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_339
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.leaf (-4)) (.branch 23 (.leaf (-3)) (.leaf (-2)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_340 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_340
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 19 (.leaf (-18)) (.branch 23 (.leaf (-14)) (.leaf (-7)))),
  (.branch 17 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (0)))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 18 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_341 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_341
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-14)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-22)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 17 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 19 (.leaf (-18)) (.branch 23 (.leaf (-14)) (.leaf (-7)))),
  (.branch 17 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 21 (.branch 7 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 22 (.leaf (-17)) (.branch 23 (.leaf (-14)) (.leaf (-11))))),
  (.branch 12 (.branch 11 (.leaf (-3)) (.leaf (-2))) (.branch 13 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_342 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_342
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6)))]
  high := ![(.leaf (-8)),
  (.branch 13 (.branch 3 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 23 (.leaf (-8)) (.leaf (-6)))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_343 : CycleWitness 6 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (3)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_343
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-15))),
  (.branch 19 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 18 (.leaf (-4)) (.branch 22 (.leaf (-3)) (.leaf (-2)))),
  (.branch 11 (.branch 3 (.leaf (-11)) (.branch 7 (.leaf (-10)) (.leaf (-9)))) (.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))),
  (.branch 17 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-15)) (.branch 10 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 12 (.leaf (-12)) (.leaf (-11))) (.branch 14 (.leaf (-10)) (.leaf (-9))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-7))) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_344 : CycleWitness 6 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_344
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 15 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 17 (.branch 4 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-11)) (.leaf (-8)))),
  (.branch 3 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-4)))),
  (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 21 (.leaf (-4)) (.branch 22 (.leaf (-3)) (.leaf (-2))))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.branch 12 (.leaf (-3)) (.leaf (-2))) (.branch 14 (.leaf (-1)) (.leaf (0))))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-7))) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_345 : CycleWitness 6 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_345
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-14))),
  (.branch 20 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 15 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 22 (.leaf (-14)) (.leaf (-7)))),
  (.branch 20 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-2)) (.leaf (0)))),
  (.branch 13 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-4)))),
  (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-12)) (.leaf (-10)))) (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-6))) (.branch 22 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-14)) (.branch 11 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.branch 13 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.leaf (-8))))) (.branch 19 (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_346 : CycleWitness 6 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_346
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 10 (.leaf (-10)) (.leaf (-12)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-6)) (.leaf (-10))))]
  high := ![(.branch 10 (.branch 2 (.leaf (-17)) (.branch 6 (.leaf (-16)) (.leaf (-15)))) (.branch 18 (.branch 14 (.leaf (-14)) (.leaf (-13))) (.branch 22 (.leaf (-12)) (.leaf (-6))))),
  (.branch 16 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (-3)),
  (.branch 20 (.branch 4 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 19 (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8)))) (.branch 21 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 22 (.leaf (-5)) (.leaf (-4)))))]
def witnessD6_012_347 : CycleWitness 6 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (5)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_347
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-12)) (.leaf (-6)))),
  (.branch 8 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.branch 4 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 16 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 7 (.leaf (-11)) (.branch 19 (.leaf (-10)) (.leaf (-8)))) (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-4)) (.leaf (-2)))))]
def witnessD6_012_348 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_348
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 13 (.leaf (-10)) (.leaf (-11)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-11)) (.branch 21 (.leaf (-10)) (.leaf (-6)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 7 (.leaf (-16)) (.leaf (-15)))) (.branch 10 (.branch 9 (.leaf (-14)) (.leaf (-13))) (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_012_349 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 5 (.leaf (0)) (.leaf (4)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))))
  code := certificateD6_349
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))) (.branch 19 (.branch 18 (.leaf (11)) (.leaf (12))) (.branch 21 (.leaf (13)) (.leaf (14)))))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-8)) (.branch 8 (.leaf (-9)) (.leaf (-10))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-10)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_350 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (0))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_350
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 16 (.branch 14 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_351 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_351
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 18 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-6)) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_352 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_352
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-5))),
  (.branch 14 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-3)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_353 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (5)))))))
  code := certificateD6_353
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 20 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-5))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_354 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_354
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-17)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 10 (.leaf (-5)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 14 (.leaf (-15)) (.branch 19 (.leaf (-14)) (.leaf (-9))))),
  (.branch 21 (.leaf (-10)) (.leaf (-7))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 8 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6))))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_355 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_355
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 11 (.leaf (-10)) (.leaf (-11)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-4))))),
  (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-10)) (.leaf (-7)))),
  (.branch 11 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.leaf (0)))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_356 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_356
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 18 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-5)) (.leaf (-3)))),
  (.branch 9 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_012_357 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (2)) (.leaf (1)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_357
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 6 (.leaf (-17)) (.leaf (-18)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.branch 17 (.leaf (-8)) (.leaf (-11))))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 20 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-12)) (.leaf (-7)))),
  (.branch 18 (.leaf (-11)) (.leaf (-7))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-13)) (.branch 11 (.leaf (-12)) (.leaf (-11)))) (.branch 13 (.leaf (-10)) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_012_358 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_358
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 7 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 19 (.leaf (-9)) (.leaf (-5))),
  (.branch 19 (.branch 10 (.leaf (-17)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_359 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_359
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-18)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 9 (.leaf (-10)) (.leaf (-7))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_012_360 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (5)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_360
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-9)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 13 (.leaf (-7)) (.leaf (-6))) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.branch 18 (.leaf (-11)) (.leaf (-9))) (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-5)) (.leaf (-3))))),
  (.branch 7 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (0)))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_361 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (0)) (.leaf (2)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_361
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 13 (.leaf (-7)) (.leaf (-6))) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_362 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_362
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_363 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (4)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_363
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 13 (.branch 10 (.leaf (-17)) (.leaf (-18))) (.branch 16 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.leaf (-20)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 6 (.leaf (-9)) (.leaf (-7))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_364 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_364
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_012_365 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_365
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 19 (.leaf (-14)) (.leaf (-9))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-8)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.branch 12 (.leaf (-3)) (.leaf (-2))) (.branch 14 (.leaf (-1)) (.leaf (0))))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_366 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (4)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_366
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_012_367 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_367
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 16 (.leaf (-16)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.leaf (-18)) (.branch 21 (.leaf (-13)) (.leaf (-7)))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_368 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_368
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 10 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 14 (.leaf (-19)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 12 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 20 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3))))),
  (.branch 17 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6))))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_012_369 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (5)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_369
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_012_370 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (4)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_370
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-22)))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-24)))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-7))),
  (.branch 15 (.branch 5 (.leaf (-22)) (.branch 10 (.leaf (-21)) (.leaf (-20)))) (.branch 20 (.leaf (-19)) (.branch 21 (.leaf (-15)) (.leaf (-11))))),
  (.branch 17 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22)))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))),
  (.leaf (-1))]
def witnessD6_012_371 : CycleWitness 6 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_371
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 21 (.leaf (-10)) (.leaf (-5)))),
  (.branch 18 (.leaf (-2)) (.leaf (0))),
  (.branch 19 (.branch 11 (.leaf (-14)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-5)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_012 : Fin 43 → CycleWitness 6 := ![witnessD6_012_329, witnessD6_012_330, witnessD6_012_331, witnessD6_012_332, witnessD6_012_333, witnessD6_012_334, witnessD6_012_335, witnessD6_012_336, witnessD6_012_337, witnessD6_012_338, witnessD6_012_339, witnessD6_012_340, witnessD6_012_341, witnessD6_012_342, witnessD6_012_343, witnessD6_012_344, witnessD6_012_345, witnessD6_012_346, witnessD6_012_347, witnessD6_012_348, witnessD6_012_349, witnessD6_012_350, witnessD6_012_351, witnessD6_012_352, witnessD6_012_353, witnessD6_012_354, witnessD6_012_355, witnessD6_012_356, witnessD6_012_357, witnessD6_012_358, witnessD6_012_359, witnessD6_012_360, witnessD6_012_361, witnessD6_012_362, witnessD6_012_363, witnessD6_012_364, witnessD6_012_365, witnessD6_012_366, witnessD6_012_367, witnessD6_012_368, witnessD6_012_369, witnessD6_012_370, witnessD6_012_371]
end RealPinwheel.FiveSixths


