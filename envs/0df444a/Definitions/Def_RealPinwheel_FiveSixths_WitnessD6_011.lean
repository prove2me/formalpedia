-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_011
-- name    : RealPinwheel_FiveSixths_WitnessD6_011
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:40:15.91619+00:00
-- url     : https://prove2.me/theorems/3ad9aec2-ab4b-4259-91a0-c94094fc3575
-- title:
--   Exact witness block D6_011
-- statement:
--   These exact witnesses represent words 291 through 329 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 291–329; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_011_290 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (3)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (4)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (3)) (.leaf (4)))))))
  code := certificateD6_290
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 14 (.branch 6 (.branch 2 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 18 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 22 (.branch 19 (.branch 5 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-16)) (.branch 21 (.leaf (-14)) (.leaf (-12))))) (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-8))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-4)) (.leaf (-2))))))]
def witnessD6_011_291 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (4))) (.branch 19 (.leaf (1)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (5)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_291
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 19 (.leaf (-16)) (.leaf (-19)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 14 (.branch 6 (.branch 2 (.leaf (-20)) (.leaf (-19))) (.branch 10 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 18 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-14)) (.leaf (-10)))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 25 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 7 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))))]
def witnessD6_011_292 : CycleWitness 6 where
  length := 27
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 18 (.branch 17 (.leaf (3)) (.leaf (5))) (.branch 19 (.leaf (0)) (.leaf (2))))) (.branch 23 (.branch 21 (.leaf (1)) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_292
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 25 (.branch 24 (.leaf (-8)) (.leaf (-6))) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 3 (.leaf (-5)) (.branch 26 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5)))),
  (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2)))),
  (.branch 23 (.branch 14 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.branch 26 (.leaf (-3)) (.leaf (-2))))))]
def witnessD6_011_293 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (0))) (.branch 23 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_293
  counts := ![(.branch 12 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 24 (.leaf (14)) (.branch 25 (.leaf (15)) (.leaf (16))))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_294 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (4)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (3))))) (.branch 23 (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_294
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 23 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 24 (.leaf (-8)) (.leaf (-7))))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-4)) (.leaf (-2))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_011_295 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_295
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 18 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-5)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_011_296 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_296
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 15 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_011_297 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_297
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 7 (.leaf (-9)) (.branch 9 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.leaf (-11)) (.leaf (-6))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_298 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_298
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 18 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 21 (.leaf (-10)) (.leaf (-6))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_299 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_299
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-6)) (.leaf (-4))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_011_300 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_300
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 22 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 24 (.branch 18 (.leaf (-16)) (.leaf (-13))) (.branch 25 (.leaf (-9)) (.leaf (-5)))),
  (.branch 5 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (0)))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_011_301 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_301
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-21)))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-16)))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.branch 8 (.branch 4 (.leaf (-28)) (.leaf (-27))) (.branch 12 (.leaf (-26)) (.leaf (-25)))) (.branch 24 (.branch 20 (.leaf (-24)) (.leaf (-23))) (.branch 25 (.leaf (-17)) (.leaf (-11))))),
  (.branch 17 (.branch 9 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19)))) (.branch 21 (.leaf (-18)) (.branch 25 (.leaf (-17)) (.leaf (-11))))),
  (.branch 18 (.leaf (-3)) (.leaf (0))),
  (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))),
  (.leaf (-1))]
def witnessD6_011_302 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_302
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 20 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9)))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_011_303 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (3)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_303
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-12)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-6))))]
  high := ![(.branch 13 (.branch 7 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 10 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 22 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 15 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-12)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.leaf (-3))))]
def witnessD6_011_304 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (5)) (.leaf (3)))))))
  code := certificateD6_304
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.branch 23 (.leaf (-20)) (.leaf (-23))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 8 (.leaf (-13)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 25 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 24 (.leaf (-23)) (.branch 25 (.leaf (-16)) (.leaf (-9)))),
  (.branch 17 (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-8))))),
  (.branch 23 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_011_305 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_305
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.branch 24 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 16 (.branch 11 (.branch 8 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16))))) (.branch 13 (.branch 12 (.leaf (-15)) (.leaf (-14))) (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_306 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_306
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.branch 24 (.leaf (-7)) (.leaf (-8))))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 25 (.leaf (-8)) (.leaf (-5))),
  (.branch 22 (.branch 4 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_011_307 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_307
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_308 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_308
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 12 (.leaf (-15)) (.leaf (-14)))) (.branch 15 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 16 (.leaf (-11)) (.leaf (-10))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_011_309 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_309
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-18))),
  (.branch 21 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-5)) (.leaf (-4))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.branch 19 (.leaf (-3)) (.leaf (-2))) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 12 (.branch 10 (.branch 9 (.leaf (-18)) (.leaf (-17))) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 14 (.branch 13 (.leaf (-14)) (.leaf (-13))) (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_310 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (2)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (5)))))))
  code := certificateD6_310
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-19))) (.branch 15 (.leaf (-24)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.branch 3 (.leaf (-12)) (.leaf (-11))) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD6_011_311 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_311
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 25 (.leaf (9)) (.leaf (10)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-5)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 24 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.branch 17 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_011_312 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (5)))))))
  code := certificateD6_312
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-11)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 23 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD6_011_313 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (5)))))))
  code := certificateD6_313
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.branch 15 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 21 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.leaf (0))]
def witnessD6_011_314 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (4)))))))
  code := certificateD6_314
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 18 (.leaf (-19)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 5 (.leaf (-6)) (.leaf (-5))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_315 : CycleWitness 6 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_315
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-7)) (.leaf (-5))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_011_316 : CycleWitness 6 where
  length := 25
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (5)) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 23 (.leaf (1)) (.branch 24 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_316
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.leaf (13)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-12)) (.leaf (-24)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))) (.branch 19 (.branch 15 (.leaf (-9)) (.leaf (-10))) (.branch 23 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 13 (.branch 7 (.branch 3 (.leaf (-24)) (.branch 5 (.leaf (-23)) (.leaf (-22)))) (.branch 9 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 15 (.leaf (-18)) (.branch 17 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))),
  (.branch 24 (.leaf (-12)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-6))) (.branch 24 (.leaf (-4)) (.leaf (-2)))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-7))) (.branch 20 (.leaf (-6)) (.leaf (-5)))) (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-20)) (.leaf (-19))) (.branch 8 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16))))) (.branch 12 (.branch 11 (.leaf (-15)) (.leaf (-14))) (.branch 13 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-11)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_011_317 : CycleWitness 6 where
  length := 25
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (2)) (.leaf (0)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_317
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 22 (.branch 20 (.leaf (11)) (.leaf (12))) (.branch 24 (.leaf (13)) (.leaf (14)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 18 (.leaf (-22)) (.leaf (-23)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-8)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 21 (.branch 19 (.leaf (-23)) (.leaf (-20))) (.branch 23 (.leaf (-17)) (.leaf (-14)))),
  (.branch 22 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-6)) (.leaf (-4))))),
  (.branch 21 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.branch 8 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6)))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-7)) (.leaf (-6)))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-20)) (.leaf (-19))) (.branch 8 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16))))) (.branch 12 (.branch 11 (.leaf (-15)) (.leaf (-14))) (.branch 13 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-11)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_011_318 : CycleWitness 6 where
  length := 25
  word := (.branch 13 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (5)) (.leaf (0)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 23 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_318
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 23 (.leaf (10)) (.leaf (11)))))),
  (.branch 13 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-13)) (.leaf (-26)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 13 (.leaf (-8)) (.branch 20 (.leaf (-9)) (.leaf (-10))))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-6)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 22 (.leaf (0)) (.leaf (-3))),
  (.branch 15 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 10 (.branch 3 (.leaf (-26)) (.leaf (-25))) (.branch 17 (.leaf (-24)) (.branch 24 (.leaf (-23)) (.leaf (-13))))),
  (.branch 21 (.leaf (-10)) (.leaf (-7))),
  (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6))))),
  (.branch 12 (.leaf (-2)) (.branch 13 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_011_319 : CycleWitness 6 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_319
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))),
  (.branch 16 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 20 (.leaf (-19)) (.branch 24 (.leaf (-18)) (.leaf (-13))))),
  (.branch 22 (.branch 4 (.leaf (-16)) (.branch 21 (.leaf (-15)) (.leaf (-12)))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-16)) (.leaf (-14))) (.branch 20 (.leaf (-12)) (.leaf (-10)))) (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-6))) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 10 (.leaf (-7)) (.leaf (-6))) (.branch 24 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0))]
def witnessD6_011_320 : CycleWitness 6 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (5)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (3)))))))
  code := certificateD6_320
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 23 (.branch 14 (.leaf (-19)) (.leaf (-16))) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 20 (.leaf (-8)) (.leaf (-6))),
  (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-12))) (.branch 24 (.leaf (-8)) (.leaf (-4)))),
  (.branch 13 (.leaf (-2)) (.branch 21 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.leaf (-8)) (.branch 24 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.branch 18 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 19 (.leaf (-14)) (.leaf (-12)))) (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-8))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2))))))]
def witnessD6_011_321 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (4)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_321
  counts := ![(.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.branch 23 (.leaf (15)) (.leaf (16))))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_011_322 : CycleWitness 6 where
  length := 24
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (4)) (.leaf (0)))) (.branch 21 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_322
  counts := ![(.branch 12 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 21 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 23 (.leaf (14)) (.leaf (15)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_011_323 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (4)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_323
  counts := ![(.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.branch 23 (.leaf (15)) (.leaf (16))))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-6)))]
  high := ![(.leaf (-2)),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011_324 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_324
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 16 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_011_325 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (1)))))))
  code := certificateD6_325
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 14 (.branch 9 (.branch 7 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 8 (.leaf (-17)) (.leaf (-16)))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 17 (.branch 14 (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))) (.branch 15 (.leaf (-10)) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_011_326 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_326
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 21 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_011_327 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (2))))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2))))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_327
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.leaf (12)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-13))),
  (.branch 23 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 14 (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))) (.branch 15 (.leaf (-10)) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_011_328 : CycleWitness 6 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_328
  counts := ![(.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 16 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 15 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 9 (.branch 6 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 7 (.leaf (-18)) (.branch 8 (.leaf (-17)) (.leaf (-16))))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_011 : Fin 39 → CycleWitness 6 := ![witnessD6_011_290, witnessD6_011_291, witnessD6_011_292, witnessD6_011_293, witnessD6_011_294, witnessD6_011_295, witnessD6_011_296, witnessD6_011_297, witnessD6_011_298, witnessD6_011_299, witnessD6_011_300, witnessD6_011_301, witnessD6_011_302, witnessD6_011_303, witnessD6_011_304, witnessD6_011_305, witnessD6_011_306, witnessD6_011_307, witnessD6_011_308, witnessD6_011_309, witnessD6_011_310, witnessD6_011_311, witnessD6_011_312, witnessD6_011_313, witnessD6_011_314, witnessD6_011_315, witnessD6_011_316, witnessD6_011_317, witnessD6_011_318, witnessD6_011_319, witnessD6_011_320, witnessD6_011_321, witnessD6_011_322, witnessD6_011_323, witnessD6_011_324, witnessD6_011_325, witnessD6_011_326, witnessD6_011_327, witnessD6_011_328]
end RealPinwheel.FiveSixths


