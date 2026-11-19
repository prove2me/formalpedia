-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_224
-- name    : RealPinwheel_FiveSixths_WitnessD8_224
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:04:14.053371+00:00
-- url     : https://prove2.me/theorems/81c80a99-631f-40ed-83c9-683709b79181
-- title:
--   Exact witness block D8_224
-- statement:
--   These exact witnesses represent words 2833 through 2860 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2833–2860; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_224_2832 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (2)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (7)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_2832
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_224_2833 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (7))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (4)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (1))) (.branch 30 (.leaf (3)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2833
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-29))) (.branch 11 (.leaf (-30)) (.branch 16 (.leaf (-31)) (.leaf (-32))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 14 (.leaf (-9)) (.leaf (-10)))) (.branch 29 (.branch 24 (.leaf (-11)) (.leaf (-12))) (.branch 34 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-15)) (.leaf (-20)))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-5)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 33 (.branch 17 (.leaf (-32)) (.leaf (-28))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.leaf (-14)) (.leaf (-7))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 31 (.branch 29 (.branch 16 (.leaf (-20)) (.leaf (-19))) (.branch 30 (.leaf (-17)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-13)) (.leaf (-11))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-7)) (.leaf (-5)))))),
  (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (0))]
def witnessD8_224_2834 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (5)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2834
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 27 (.leaf (-15)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 31 (.leaf (-14)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.branch 28 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-10)) (.leaf (-7))))),
  (.leaf (-1)),
  (.branch 34 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-14))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 29 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_224_2835 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (7)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2835
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_224_2836 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (7)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (3)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (2)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (7)) (.leaf (1))))))))
  code := certificateD8_2836
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-26)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 26 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 9 (.leaf (-26)) (.branch 31 (.leaf (-25)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-17)) (.leaf (-13))) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 27 (.leaf (-12)) (.branch 35 (.leaf (-9)) (.leaf (-5)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_224_2837 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (5))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (6)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (7))) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (5))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2837
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-21))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 3 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-17)))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 21 (.leaf (-7)) (.leaf (-5))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_224_2838 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (7)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (6)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (5)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (7)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2838
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_224_2839 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2839
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))) (.branch 26 (.leaf (-3)) (.branch 30 (.leaf (-4)) (.leaf (-5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 23 (.leaf (-22)) (.leaf (-24)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 32 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.branch 31 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-3)))) (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 24 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-17)))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 6 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-5)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_224_2840 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (1)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2840
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 30 (.leaf (-6)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.leaf (-8)) (.leaf (-7))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_224_2841 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (6)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (7)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2841
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-21)) (.leaf (-22)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 19 (.leaf (-7)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 28 (.branch 7 (.leaf (-22)) (.leaf (-21))) (.branch 34 (.leaf (-17)) (.branch 35 (.leaf (-12)) (.leaf (-7))))),
  (.branch 25 (.leaf (-10)) (.leaf (-7))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_224_2842 : CycleWitness 8 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (7)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (2))) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (3)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (5)) (.leaf (2))) (.branch 30 (.leaf (1)) (.leaf (6)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2842
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-29)) (.leaf (-30)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))) (.branch 19 (.leaf (-10)) (.branch 24 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 33 (.branch 7 (.leaf (-30)) (.leaf (-28))) (.branch 34 (.leaf (-21)) (.branch 35 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-12)) (.leaf (-7))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_224_2843 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2843
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 22 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 33 (.leaf (14)) (.leaf (15)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-28))),
  (.branch 14 (.leaf (0)) (.leaf (-21))),
  (.branch 21 (.leaf (0)) (.leaf (-14))),
  (.branch 28 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 34 (.leaf (-6)) (.leaf (-3))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-28)) (.branch 9 (.leaf (-27)) (.leaf (-26)))) (.branch 12 (.branch 11 (.leaf (-25)) (.leaf (-24))) (.branch 13 (.leaf (-23)) (.leaf (-22))))) (.branch 17 (.branch 15 (.leaf (-21)) (.branch 16 (.leaf (-20)) (.leaf (-19)))) (.branch 19 (.branch 18 (.leaf (-18)) (.leaf (-17))) (.branch 20 (.leaf (-16)) (.leaf (-15)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.leaf (-8))))) (.branch 31 (.branch 29 (.leaf (-7)) (.branch 30 (.leaf (-6)) (.leaf (-5)))) (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-21)) (.leaf (-20))) (.branch 17 (.leaf (-19)) (.branch 18 (.leaf (-18)) (.leaf (-17))))) (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.leaf (-8))))) (.branch 31 (.branch 29 (.leaf (-7)) (.branch 30 (.leaf (-6)) (.leaf (-5)))) (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 29 (.leaf (-7)) (.branch 30 (.leaf (-6)) (.leaf (-5)))) (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_224_2844 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_2844
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-18)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 10 (.leaf (-17)) (.branch 31 (.leaf (-18)) (.leaf (-19))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-17)) (.leaf (-18)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-22))),
  (.branch 30 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-18)) (.leaf (-14))))),
  (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 27 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.leaf (-5)) (.leaf (-4))),
  (.branch 32 (.branch 30 (.leaf (-18)) (.branch 31 (.leaf (-15)) (.leaf (-12)))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-22)) (.leaf (-21))) (.branch 16 (.leaf (-20)) (.branch 17 (.leaf (-19)) (.leaf (-18))))) (.branch 21 (.branch 19 (.leaf (-17)) (.branch 20 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_224_2845 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2845
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-18)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 10 (.leaf (-17)) (.branch 31 (.leaf (-18)) (.leaf (-19))))),
  (.branch 23 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 17 (.leaf (0)) (.leaf (-18))),
  (.branch 34 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-18)) (.leaf (-14))))),
  (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 24 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-18)) (.leaf (-17))) (.branch 20 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-11)) (.leaf (-10)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD8_224_2846 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (7)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2846
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-23)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-23)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-21))),
  (.branch 29 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-34)) (.branch 7 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29))))) (.branch 28 (.branch 22 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 26 (.branch 14 (.branch 8 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-18))) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))),
  (.branch 18 (.branch 9 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 28 (.branch 25 (.branch 5 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-21)) (.leaf (-20))) (.branch 17 (.leaf (-19)) (.branch 18 (.leaf (-18)) (.leaf (-17))))) (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_224_2847 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (6))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (7)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2847
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-23)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-23)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-9))))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-34)) (.branch 7 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29))))) (.branch 28 (.branch 22 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 26 (.branch 14 (.branch 8 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-18))) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))),
  (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 30 (.branch 27 (.branch 9 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 25 (.branch 5 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 32 (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7)))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))))]
def witnessD8_224_2848 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (6))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (7))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (5))))))))
  code := certificateD8_2848
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-23)) (.leaf (-29)))),
  (.branch 2 (.leaf (0)) (.branch 31 (.leaf (-23)) (.leaf (-24)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-13)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-20)) (.leaf (-21)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-23)) (.leaf (-24)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (-5)) (.leaf (-6))))]
  high := ![(.branch 25 (.branch 19 (.leaf (-29)) (.branch 22 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.branch 28 (.leaf (-26)) (.leaf (-25))) (.branch 34 (.leaf (-24)) (.leaf (-12))))),
  (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-18))) (.branch 34 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 20 (.branch 10 (.leaf (-20)) (.leaf (-19))) (.branch 30 (.leaf (-18)) (.leaf (-16)))) (.branch 33 (.branch 32 (.leaf (-14)) (.leaf (-12))) (.branch 34 (.leaf (-10)) (.leaf (-8))))),
  (.branch 31 (.branch 29 (.leaf (-21)) (.branch 30 (.leaf (-18)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-24)) (.branch 25 (.leaf (-22)) (.leaf (-20)))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-16)) (.leaf (-14))))) (.branch 32 (.branch 30 (.leaf (-12)) (.branch 31 (.leaf (-10)) (.leaf (-8)))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_224_2849 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (7)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (6)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_2849
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-23)) (.leaf (-33)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.branch 26 (.leaf (-16)) (.leaf (-22))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-8)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 19 (.branch 10 (.branch 7 (.leaf (-33)) (.leaf (-32))) (.branch 13 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29))))) (.branch 28 (.branch 22 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 33 (.branch 27 (.leaf (-22)) (.leaf (-19))) (.branch 34 (.leaf (-15)) (.leaf (-11)))),
  (.branch 31 (.branch 21 (.branch 12 (.leaf (-26)) (.leaf (-25))) (.branch 30 (.leaf (-24)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5))))),
  (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-6))) (.branch 34 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 17 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_224_2850 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (7)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_2850
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-23)) (.leaf (-33)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.branch 26 (.leaf (-16)) (.leaf (-22))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-8)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.leaf (-21))),
  (.branch 31 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 19 (.branch 10 (.branch 7 (.leaf (-33)) (.leaf (-32))) (.branch 13 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29))))) (.branch 28 (.branch 22 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 33 (.branch 27 (.leaf (-22)) (.leaf (-19))) (.branch 34 (.leaf (-15)) (.leaf (-11)))),
  (.branch 31 (.branch 21 (.branch 12 (.leaf (-26)) (.leaf (-25))) (.branch 30 (.leaf (-24)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5))))),
  (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-21)) (.leaf (-20))) (.branch 17 (.leaf (-19)) (.branch 18 (.leaf (-18)) (.leaf (-17))))) (.branch 21 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_224_2851 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (7)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (6)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2851
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-26)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 4 (.leaf (0)) (.leaf (-19))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-14)) (.leaf (-16)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 26 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 21 (.branch 13 (.branch 9 (.leaf (-33)) (.leaf (-32))) (.branch 17 (.leaf (-31)) (.leaf (-30)))) (.branch 29 (.branch 25 (.leaf (-29)) (.leaf (-28))) (.branch 33 (.leaf (-27)) (.branch 34 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 30 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 4 (.leaf (-17)) (.branch 10 (.leaf (-16)) (.leaf (-15)))) (.branch 28 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.branch 5 (.leaf (-19)) (.branch 14 (.leaf (-18)) (.leaf (-17)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.branch 19 (.leaf (-16)) (.branch 31 (.leaf (-15)) (.leaf (-12)))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-24)) (.branch 13 (.leaf (-23)) (.leaf (-22)))) (.branch 15 (.leaf (-21)) (.branch 16 (.leaf (-20)) (.leaf (-19))))) (.branch 20 (.branch 18 (.leaf (-18)) (.branch 19 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.leaf (-15)) (.branch 22 (.leaf (-14)) (.leaf (-13)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-11)) (.leaf (-10)))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_224_2852 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (3)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (6)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2852
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-26)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 29 (.branch 21 (.leaf (-30)) (.branch 25 (.leaf (-29)) (.leaf (-28)))) (.branch 33 (.leaf (-27)) (.branch 34 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-2)),
  (.branch 32 (.branch 30 (.leaf (-24)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-21))) (.branch 30 (.leaf (-18)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.leaf (-6)) (.leaf (-3))),
  (.branch 32 (.branch 7 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.branch 19 (.leaf (-1)) (.leaf (0)))))]
def witnessD8_224_2853 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_2853
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-6)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 30 (.branch 26 (.leaf (-6)) (.leaf (-5))) (.branch 34 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-21))) (.branch 30 (.leaf (-18)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 8 (.leaf (-6)) (.leaf (-5))),
  (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_224_2854 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (7)) (.branch 16 (.leaf (4)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (6)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_2854
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 26 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 29 (.leaf (-16)) (.leaf (-19)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.branch 18 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 4 (.leaf (0)) (.leaf (-23))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 30 (.leaf (-19)) (.branch 34 (.leaf (-18)) (.leaf (-14)))),
  (.branch 33 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-6)) (.leaf (-4)))),
  (.branch 31 (.branch 13 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.branch 8 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 17 (.branch 5 (.leaf (-23)) (.leaf (-22))) (.branch 29 (.leaf (-21)) (.leaf (-18)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 11 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.branch 19 (.leaf (-1)) (.leaf (0)))))]
def witnessD8_224_2855 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (7))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2855
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-26)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-25)) (.leaf (-26)))),
  (.branch 13 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-17))),
  (.branch 34 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.branch 9 (.branch 5 (.leaf (-34)) (.leaf (-33))) (.branch 13 (.leaf (-32)) (.branch 17 (.leaf (-31)) (.leaf (-30))))) (.branch 29 (.branch 25 (.leaf (-29)) (.leaf (-28))) (.branch 33 (.leaf (-27)) (.branch 34 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-26)) (.branch 24 (.leaf (-24)) (.leaf (-22)))) (.branch 26 (.leaf (-20)) (.branch 27 (.leaf (-18)) (.leaf (-16))))) (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-12)) (.leaf (-10)))) (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-6))) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 32 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 28 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 29 (.leaf (-14)) (.leaf (-12)))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-4))]
def witnessD8_224_2856 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (6))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (1)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (3)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_2856
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-23)) (.leaf (-25)))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 24 (.leaf (-6)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 33 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-6)) (.leaf (-4)))),
  (.branch 32 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 25 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))),
  (.branch 32 (.branch 30 (.leaf (-24)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.leaf (-2)) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.branch 18 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 31 (.branch 29 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))))]
def witnessD8_224_2857 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (2)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (7)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (6)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (4)) (.branch 34 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2857
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 26 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 33 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-17)) (.leaf (-18)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.branch 6 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-11)) (.leaf (-6))))),
  (.branch 32 (.branch 23 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-9)) (.leaf (-7))),
  (.branch 32 (.branch 30 (.leaf (-18)) (.branch 31 (.leaf (-15)) (.leaf (-12)))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 17 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_224_2858 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (7)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2858
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 27 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 34 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.leaf (-26))),
  (.branch 26 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 28 (.leaf (-15)) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 32 (.branch 20 (.leaf (-26)) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-7)),
  (.branch 32 (.branch 22 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-26)) (.branch 11 (.leaf (-25)) (.leaf (-24)))) (.branch 13 (.leaf (-23)) (.branch 14 (.leaf (-22)) (.leaf (-21))))) (.branch 18 (.branch 16 (.leaf (-20)) (.branch 17 (.leaf (-19)) (.leaf (-18)))) (.branch 20 (.branch 19 (.leaf (-17)) (.leaf (-16))) (.branch 21 (.leaf (-15)) (.leaf (-14)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-13)) (.branch 24 (.leaf (-12)) (.leaf (-11)))) (.branch 26 (.leaf (-10)) (.branch 27 (.leaf (-9)) (.leaf (-8))))) (.branch 31 (.branch 29 (.leaf (-7)) (.branch 30 (.leaf (-6)) (.leaf (-5)))) (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_224_2859 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (6)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (7)) (.leaf (2))) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (6))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2859
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 30 (.leaf (-26)) (.leaf (-27)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-5)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 32 (.branch 31 (.leaf (-27)) (.leaf (-23))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-15)) (.leaf (-11))))),
  (.branch 32 (.branch 20 (.leaf (-26)) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.leaf (-8)) (.branch 29 (.leaf (-7)) (.leaf (-6)))),
  (.branch 25 (.leaf (-9)) (.branch 34 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 30 (.leaf (-24)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 30 (.branch 28 (.branch 10 (.leaf (-17)) (.leaf (-16))) (.branch 29 (.leaf (-14)) (.leaf (-12)))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_224 : Fin 28 → CycleWitness 8 := ![witnessD8_224_2832, witnessD8_224_2833, witnessD8_224_2834, witnessD8_224_2835, witnessD8_224_2836, witnessD8_224_2837, witnessD8_224_2838, witnessD8_224_2839, witnessD8_224_2840, witnessD8_224_2841, witnessD8_224_2842, witnessD8_224_2843, witnessD8_224_2844, witnessD8_224_2845, witnessD8_224_2846, witnessD8_224_2847, witnessD8_224_2848, witnessD8_224_2849, witnessD8_224_2850, witnessD8_224_2851, witnessD8_224_2852, witnessD8_224_2853, witnessD8_224_2854, witnessD8_224_2855, witnessD8_224_2856, witnessD8_224_2857, witnessD8_224_2858, witnessD8_224_2859]
end RealPinwheel.FiveSixths


