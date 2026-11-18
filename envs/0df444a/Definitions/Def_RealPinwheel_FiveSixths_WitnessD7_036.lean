-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_036
-- name    : RealPinwheel_FiveSixths_WitnessD7_036
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:12.533218+00:00
-- url     : https://prove2.me/theorems/01c58fbb-230e-4453-984a-2bf9a860028d
-- title:
--   Exact witness block D7_036
-- statement:
--   These exact witnesses represent words 474 through 493 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 474–493; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_036_473 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_473
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 29 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 42 (.branch 39 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 41 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.leaf (15)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 38 (.leaf (-7)) (.leaf (-5))),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 31 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_036_474 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (5)) (.leaf (0))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (2)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (6)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_474
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 31 (.branch 27 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 43 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 32 (.leaf (5)) (.leaf (6))) (.branch 44 (.leaf (7)) (.branch 48 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))) (.branch 33 (.branch 20 (.leaf (-9)) (.leaf (-10))) (.branch 36 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-41))),
  (.branch 23 (.leaf (0)) (.leaf (-25))),
  (.branch 39 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 37 (.leaf (-12)) (.branch 44 (.leaf (-11)) (.leaf (-9)))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 33 (.leaf (-2)) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-41)) (.leaf (-40))) (.branch 10 (.leaf (-39)) (.branch 11 (.leaf (-38)) (.leaf (-37))))) (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.branch 16 (.leaf (-33)) (.leaf (-32)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-31)) (.leaf (-30))) (.branch 20 (.leaf (-29)) (.branch 21 (.leaf (-28)) (.leaf (-27))))) (.branch 24 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))))) (.branch 37 (.branch 32 (.branch 29 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 30 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17))))) (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 29 (.branch 26 (.branch 24 (.leaf (-25)) (.branch 25 (.leaf (-24)) (.leaf (-23)))) (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20))))) (.branch 32 (.branch 30 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17)))) (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-15)) (.leaf (-14)))))) (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_036_475 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (1)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_475
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 29 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 7 (.leaf (-20)) (.leaf (-23)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 15 (.leaf (-4)) (.branch 39 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 39 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 40 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))),
  (.branch 45 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_036_476 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_476
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 30 (.leaf (12)) (.branch 33 (.leaf (13)) (.leaf (14))))) (.branch 42 (.branch 37 (.leaf (15)) (.branch 40 (.leaf (16)) (.leaf (17)))) (.branch 45 (.leaf (18)) (.branch 47 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-29))),
  (.branch 43 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 38 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 26 (.branch 22 (.branch 20 (.leaf (-29)) (.branch 21 (.leaf (-28)) (.leaf (-27)))) (.branch 24 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.leaf (-23))))) (.branch 29 (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_036_477 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (6)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_477
  counts := ![(.branch 23 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))) (.branch 36 (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.branch 33 (.leaf (12)) (.leaf (13))))) (.branch 41 (.branch 39 (.leaf (14)) (.leaf (15))) (.branch 44 (.leaf (16)) (.branch 47 (.leaf (17)) (.leaf (18))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-35))),
  (.branch 29 (.leaf (0)) (.leaf (-19))),
  (.branch 45 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 42 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 30 (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.leaf (-32)))) (.branch 19 (.branch 18 (.leaf (-31)) (.leaf (-30))) (.branch 20 (.leaf (-29)) (.leaf (-28))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_036_478 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (6)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (1)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (4)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (6)) (.leaf (5))))))))
  code := certificateD7_478
  counts := ![(.branch 23 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 30 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 42 (.branch 39 (.leaf (12)) (.leaf (13))) (.branch 46 (.leaf (14)) (.leaf (15)))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 43 (.leaf (-14)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-1))]
def witnessD7_036_479 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (5)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (2)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (3)))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_479
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 43 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 7 (.leaf (-20)) (.leaf (-23)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.branch 44 (.leaf (-5)) (.leaf (-6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 39 (.branch 32 (.leaf (-23)) (.leaf (-22))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 46 (.branch 45 (.leaf (-6)) (.leaf (-5))) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.branch 45 (.branch 44 (.leaf (-6)) (.leaf (-5))) (.branch 46 (.leaf (-4)) (.branch 47 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_036_480 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_480
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-14)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (-14))) (.branch 33 (.leaf (-15)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 37 (.branch 28 (.leaf (-14)) (.leaf (-13))) (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-10)) (.leaf (-8))))),
  (.branch 45 (.branch 34 (.leaf (-17)) (.branch 44 (.leaf (-16)) (.leaf (-13)))) (.branch 46 (.leaf (-10)) (.branch 47 (.leaf (-7)) (.leaf (-4))))),
  (.branch 10 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_036_481 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (6)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (2)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (5)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_481
  counts := ![(.branch 21 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 38 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 30 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 43 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 47 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 26 (.leaf (-8)) (.branch 36 (.leaf (-10)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (-3)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-10)))),
  (.branch 15 (.leaf (0)) (.branch 46 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 46 (.branch 39 (.leaf (-22)) (.leaf (-21))) (.branch 47 (.leaf (-14)) (.leaf (-7)))),
  (.branch 45 (.branch 37 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))) (.branch 46 (.leaf (-8)) (.branch 47 (.leaf (-5)) (.leaf (-2))))),
  (.branch 34 (.branch 14 (.branch 4 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 45 (.branch 44 (.leaf (-23)) (.leaf (-19))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-11)) (.leaf (-7)))))),
  (.branch 28 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 40 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_036_482 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (4)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (4)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_482
  counts := ![(.branch 22 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 46 (.leaf (13)) (.leaf (14)))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-27)) (.leaf (-32)))),
  (.branch 6 (.leaf (0)) (.branch 40 (.leaf (-6)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 43 (.leaf (-18)) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 46 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 24 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 31 (.leaf (-30)) (.leaf (-29)))) (.branch 46 (.branch 45 (.leaf (-28)) (.leaf (-21))) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 41 (.leaf (-8)) (.leaf (-7))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_036_483 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (4)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (5)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_483
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 27 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (-8))) (.branch 39 (.leaf (-10)) (.leaf (-12)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9)))) (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 16 (.leaf (-2)) (.branch 34 (.leaf (-1)) (.leaf (0)))),
  (.branch 38 (.branch 33 (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_036_484 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_484
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-28))),
  (.branch 44 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 23 (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_036_485 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (1)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (3)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_485
  counts := ![(.branch 21 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 27 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 31 (.leaf (5)) (.leaf (6))) (.branch 42 (.leaf (7)) (.branch 47 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 40 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.branch 40 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_036_486 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (6)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (6)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_486
  counts := ![(.branch 21 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 25 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 30 (.leaf (5)) (.leaf (6))) (.branch 41 (.leaf (7)) (.branch 46 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.leaf (-2)) (.leaf (-1))),
  (.branch 36 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_036_487 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (6)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (6)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_487
  counts := ![(.branch 20 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 34 (.branch 25 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 39 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 27 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 45 (.branch 35 (.leaf (-22)) (.branch 40 (.leaf (-21)) (.leaf (-20)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 47 (.leaf (-4)) (.leaf (-3))),
  (.branch 44 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 45 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_036_488 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (6)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (5))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (6)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (5)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_488
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 42 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 25 (.leaf (-11)) (.branch 35 (.leaf (-13)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-27)) (.leaf (-29)))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-10)) (.leaf (-11))))]
  high := ![(.branch 40 (.branch 36 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.leaf (-13)))),
  (.branch 47 (.leaf (-4)) (.leaf (-3))),
  (.branch 45 (.branch 38 (.leaf (-29)) (.leaf (-28))) (.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.branch 14 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-3)))) (.branch 35 (.leaf (-2)) (.branch 42 (.leaf (-1)) (.leaf (0))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.branch 39 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_036_489 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (6)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (0))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (6)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (5)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_489
  counts := ![(.branch 24 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))) (.branch 36 (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.branch 33 (.leaf (14)) (.leaf (15))))) (.branch 43 (.branch 38 (.leaf (16)) (.branch 40 (.leaf (17)) (.leaf (18)))) (.branch 45 (.leaf (19)) (.branch 47 (.leaf (20)) (.leaf (21))))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.branch 30 (.leaf (3)) (.leaf (4))) (.branch 46 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 34 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_036_490 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (3)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (6)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (5)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (3)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (5)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (4)) (.branch 47 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_490
  counts := ![(.branch 21 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 45 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_036_491 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (6)) (.leaf (3)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (5)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (6)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (0)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (5)) (.leaf (3)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_491
  counts := ![(.branch 20 (.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 36 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 38 (.leaf (-12)) (.leaf (-13)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-3)) (.leaf (-5))))]
  high := ![(.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.branch 31 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 40 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-11)) (.branch 42 (.leaf (-10)) (.leaf (-9))))) (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 30 (.leaf (-5)) (.leaf (-4)))]
def witnessD7_036_492 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (4))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (5)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_492
  counts := ![(.branch 23 (.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 33 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 40 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.branch 38 (.leaf (-11)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.leaf (-13)),
  (.branch 37 (.branch 27 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 46 (.branch 39 (.leaf (-15)) (.leaf (-14))) (.branch 47 (.leaf (-12)) (.leaf (-10)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-1)) (.leaf (0)))]
def witnessD7_036 : Fin 20 → CycleWitness 7 := ![witnessD7_036_473, witnessD7_036_474, witnessD7_036_475, witnessD7_036_476, witnessD7_036_477, witnessD7_036_478, witnessD7_036_479, witnessD7_036_480, witnessD7_036_481, witnessD7_036_482, witnessD7_036_483, witnessD7_036_484, witnessD7_036_485, witnessD7_036_486, witnessD7_036_487, witnessD7_036_488, witnessD7_036_489, witnessD7_036_490, witnessD7_036_491, witnessD7_036_492]
end RealPinwheel.FiveSixths


