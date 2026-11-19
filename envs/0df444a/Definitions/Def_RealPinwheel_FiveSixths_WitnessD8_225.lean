-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_225
-- name    : RealPinwheel_FiveSixths_WitnessD8_225
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:06:25.871275+00:00
-- url     : https://prove2.me/theorems/3fe37baf-4d90-40ab-af54-811916dcd616
-- title:
--   Exact witness block D8_225
-- statement:
--   These exact witnesses represent words 2861 through 2889 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2861–2889; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_225_2860 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (7)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (5)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (6)) (.leaf (4))))))))
  code := certificateD8_2860
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-27)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-11)) (.leaf (-14)))),
  (.branch 26 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 30 (.branch 26 (.leaf (-6)) (.leaf (-5))) (.branch 34 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-24)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 24 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-21))) (.branch 30 (.leaf (-18)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-6)) (.leaf (-5))),
  (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_225_2861 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (7))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (3)) (.leaf (0)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (5)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (7))) (.branch 33 (.leaf (6)) (.branch 34 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2861
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-5)) (.branch 28 (.leaf (-6)) (.leaf (-8))))),
  (.branch 23 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 29 (.leaf (-23)) (.leaf (-28)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-23)) (.leaf (-25)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 32 (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-25)) (.leaf (-22)))) (.branch 33 (.leaf (-19)) (.branch 34 (.leaf (-16)) (.leaf (-13))))),
  (.branch 26 (.leaf (-5)) (.leaf (-4))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 30 (.branch 28 (.branch 16 (.leaf (-25)) (.leaf (-24))) (.branch 29 (.leaf (-21)) (.leaf (-18)))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-7)))),
  (.branch 33 (.branch 15 (.leaf (-7)) (.leaf (-6))) (.branch 34 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_225_2862 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (7))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (0)) (.leaf (6)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (5)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_2862
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-6)) (.branch 24 (.leaf (-9)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-26)))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 20 (.branch 8 (.branch 2 (.leaf (-29)) (.leaf (-28))) (.branch 14 (.leaf (-27)) (.leaf (-26)))) (.branch 32 (.branch 26 (.leaf (-25)) (.leaf (-24))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 34 (.leaf (-9)) (.leaf (-7)))),
  (.branch 31 (.branch 21 (.branch 12 (.leaf (-26)) (.leaf (-25))) (.branch 30 (.leaf (-24)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 30 (.branch 27 (.branch 9 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD8_225_2863 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (5)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (6))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (1))))))))
  code := certificateD8_2863
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-17)) (.branch 19 (.leaf (-22)) (.leaf (-23))))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 33 (.leaf (-6)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.branch 34 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-26))),
  (.branch 9 (.leaf (0)) (.branch 32 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 32 (.branch 20 (.leaf (-23)) (.branch 31 (.leaf (-22)) (.leaf (-19)))) (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-13)) (.leaf (-10))))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.leaf (-9)) (.leaf (-7))),
  (.leaf (-4)),
  (.branch 30 (.branch 16 (.branch 4 (.leaf (-26)) (.leaf (-25))) (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-21)) (.leaf (-18))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 24 (.branch 5 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-24)))) (.branch 26 (.branch 25 (.leaf (-22)) (.leaf (-20))) (.branch 27 (.leaf (-18)) (.leaf (-16))))) (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-12)) (.leaf (-10)))) (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-6))) (.branch 34 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_225_2864 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (1))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (6)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (7)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (5))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (6)) (.leaf (7))))))))
  code := certificateD8_2864
  counts := ![(.branch 15 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 28 (.leaf (-27)) (.leaf (-28)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-24)) (.leaf (-20)))) (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-12))) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.branch 22 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 24 (.branch 15 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0))]
def witnessD8_225_2865 : CycleWitness 8 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (7)) (.leaf (2))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (6)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (3))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2865
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-29)) (.leaf (-34)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-13)) (.leaf (-20)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 13 (.branch 7 (.leaf (-34)) (.leaf (-33))) (.branch 19 (.leaf (-32)) (.leaf (-31)))) (.branch 32 (.branch 31 (.leaf (-30)) (.leaf (-24))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-12)) (.leaf (-6)))))),
  (.branch 22 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 28 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 18 (.branch 6 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-3)))) (.branch 24 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (-23)) (.leaf (-22))) (.branch 15 (.leaf (-21)) (.leaf (-20)))) (.branch 33 (.branch 27 (.leaf (-19)) (.leaf (-18))) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 31 (.branch 29 (.leaf (-20)) (.branch 30 (.leaf (-18)) (.leaf (-16)))) (.branch 33 (.branch 32 (.leaf (-14)) (.leaf (-12))) (.branch 34 (.leaf (-10)) (.leaf (-8))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 29 (.branch 26 (.branch 8 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-16)) (.leaf (-14))))) (.branch 32 (.branch 30 (.leaf (-12)) (.branch 31 (.leaf (-10)) (.leaf (-8)))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 17 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_225_2866 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_2866
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 24 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 20 (.branch 13 (.branch 10 (.branch 8 (.leaf (-27)) (.branch 9 (.leaf (-26)) (.leaf (-25)))) (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2867 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (6))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (7))) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_2867
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.leaf (-13)))) (.branch 21 (.branch 19 (.leaf (-14)) (.leaf (-15))) (.branch 23 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-13)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-20))),
  (.branch 31 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 24 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 24 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-11)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-13)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.branch 11 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (0)))),
  (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16))))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 13 (.branch 10 (.branch 8 (.leaf (-27)) (.branch 9 (.leaf (-26)) (.leaf (-25)))) (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225_2868 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.leaf (7)) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (0)) (.leaf (2)))))))
  code := certificateD8_2868
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14))))) (.branch 30 (.branch 26 (.leaf (15)) (.branch 28 (.leaf (16)) (.leaf (17)))) (.branch 31 (.leaf (18)) (.branch 33 (.leaf (19)) (.leaf (20))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-24))),
  (.branch 27 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 25 (.leaf (-15)) (.branch 32 (.leaf (-13)) (.leaf (-10)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22)))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2869 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (5)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (6)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (4)) (.leaf (7)))))))
  code := certificateD8_2869
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 19 (.leaf (-15)) (.branch 21 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 27 (.leaf (-20)) (.leaf (-21)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-10)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_225_2870 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_2870
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 22 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-29)) (.branch 7 (.leaf (-28)) (.leaf (-27)))) (.branch 10 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 11 (.leaf (-24)) (.leaf (-23))))) (.branch 15 (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_225_2871 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.leaf (4)))))))
  code := certificateD8_2871
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_225_2872 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (7)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (0))))) (.branch 29 (.branch 27 (.leaf (3)) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (0)) (.leaf (2)))))))
  code := certificateD8_2872
  counts := ![(.branch 16 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14))))) (.branch 30 (.branch 26 (.leaf (15)) (.branch 28 (.leaf (16)) (.leaf (17)))) (.branch 31 (.leaf (18)) (.branch 33 (.leaf (19)) (.leaf (20))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 22 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 20 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-10)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-29)) (.branch 7 (.leaf (-28)) (.leaf (-27)))) (.branch 10 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 11 (.leaf (-24)) (.leaf (-23))))) (.branch 15 (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225_2873 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (6))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (1)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (7))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_2873
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-5)),
  (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2874 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_2874
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 22 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.leaf (-5)) (.branch 28 (.leaf (-4)) (.leaf (-3)))),
  (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-29)) (.branch 7 (.leaf (-28)) (.leaf (-27)))) (.branch 10 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 11 (.leaf (-24)) (.leaf (-23))))) (.branch 15 (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_225_2875 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (6))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (7))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (2)))))))
  code := certificateD8_2875
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-20))),
  (.branch 31 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16))))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2876 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (5)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_2876
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-9)))),
  (.branch 32 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2877 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_2877
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-30))),
  (.branch 21 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-5)),
  (.branch 33 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 19 (.branch 11 (.branch 7 (.branch 5 (.leaf (-30)) (.branch 6 (.leaf (-29)) (.leaf (-28)))) (.branch 9 (.branch 8 (.leaf (-27)) (.leaf (-26))) (.branch 10 (.leaf (-25)) (.leaf (-24))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2878 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (6))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (7))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_2878
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-16))) (.branch 28 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 31 (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2879 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (6)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (7)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (2)))))))
  code := certificateD8_2879
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-30))),
  (.branch 21 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 20 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-9)))),
  (.branch 32 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.leaf (-2)),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 11 (.branch 7 (.branch 5 (.leaf (-30)) (.branch 6 (.leaf (-29)) (.leaf (-28)))) (.branch 9 (.branch 8 (.leaf (-27)) (.leaf (-26))) (.branch 10 (.leaf (-25)) (.leaf (-24))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225_2880 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (7))) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.leaf (1)))))))
  code := certificateD8_2880
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2881 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (4)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (7)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (6)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (4)) (.leaf (3)))))))
  code := certificateD8_2881
  counts := ![(.branch 14 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 18 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 27 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 19 (.leaf (-22)) (.leaf (-29)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 29 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 28 (.branch 20 (.leaf (-29)) (.branch 24 (.leaf (-28)) (.leaf (-27)))) (.branch 32 (.leaf (-26)) (.branch 33 (.leaf (-22)) (.leaf (-18))))),
  (.branch 27 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.leaf (-2)),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_225_2882 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (6)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (7)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (7)) (.leaf (1)))))))
  code := certificateD8_2882
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-25)) (.leaf (-26)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 27 (.branch 15 (.leaf (-26)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_225_2883 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (6)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (5)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (7)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (5)))))))
  code := certificateD8_2883
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 19 (.leaf (-15)) (.branch 21 (.leaf (-16)) (.leaf (-17))))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 25 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 22 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-10)))),
  (.branch 28 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-26)) (.branch 10 (.leaf (-25)) (.leaf (-24)))) (.branch 12 (.leaf (-23)) (.branch 13 (.leaf (-22)) (.leaf (-21))))) (.branch 17 (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18)))) (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225_2884 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (5)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (7)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (2)) (.leaf (1)))))))
  code := certificateD8_2884
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-25)) (.leaf (-26)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.leaf (-2)),
  (.branch 29 (.branch 27 (.branch 15 (.leaf (-26)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_225_2885 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_2885
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 19 (.leaf (-15)) (.branch 21 (.leaf (-16)) (.leaf (-17))))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 20 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 22 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-10)))),
  (.branch 28 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 10 (.branch 6 (.branch 4 (.leaf (-31)) (.branch 5 (.leaf (-30)) (.leaf (-29)))) (.branch 8 (.branch 7 (.leaf (-28)) (.leaf (-27))) (.branch 9 (.leaf (-26)) (.leaf (-25))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-24)) (.leaf (-23))) (.branch 13 (.leaf (-22)) (.leaf (-21)))) (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.leaf (-17)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_225_2886 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_2886
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-28))),
  (.branch 23 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 20 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 13 (.branch 9 (.branch 7 (.leaf (-28)) (.branch 8 (.leaf (-27)) (.leaf (-26)))) (.branch 11 (.branch 10 (.leaf (-25)) (.leaf (-24))) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225_2887 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (6))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_2887
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 20 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 10 (.branch 6 (.branch 4 (.leaf (-31)) (.branch 5 (.leaf (-30)) (.leaf (-29)))) (.branch 8 (.branch 7 (.leaf (-28)) (.leaf (-27))) (.branch 9 (.leaf (-26)) (.leaf (-25))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-24)) (.leaf (-23))) (.branch 13 (.leaf (-22)) (.leaf (-21)))) (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.leaf (-17)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225_2888 : CycleWitness 8 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (6))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (2)) (.leaf (1)))))))
  code := certificateD8_2888
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-31))),
  (.branch 20 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 10 (.branch 6 (.branch 4 (.leaf (-31)) (.branch 5 (.leaf (-30)) (.leaf (-29)))) (.branch 8 (.branch 7 (.leaf (-28)) (.leaf (-27))) (.branch 9 (.leaf (-26)) (.leaf (-25))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-24)) (.leaf (-23))) (.branch 13 (.leaf (-22)) (.leaf (-21)))) (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.leaf (-17)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_225 : Fin 29 → CycleWitness 8 := ![witnessD8_225_2860, witnessD8_225_2861, witnessD8_225_2862, witnessD8_225_2863, witnessD8_225_2864, witnessD8_225_2865, witnessD8_225_2866, witnessD8_225_2867, witnessD8_225_2868, witnessD8_225_2869, witnessD8_225_2870, witnessD8_225_2871, witnessD8_225_2872, witnessD8_225_2873, witnessD8_225_2874, witnessD8_225_2875, witnessD8_225_2876, witnessD8_225_2877, witnessD8_225_2878, witnessD8_225_2879, witnessD8_225_2880, witnessD8_225_2881, witnessD8_225_2882, witnessD8_225_2883, witnessD8_225_2884, witnessD8_225_2885, witnessD8_225_2886, witnessD8_225_2887, witnessD8_225_2888]
end RealPinwheel.FiveSixths


