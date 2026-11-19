-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_214
-- name    : RealPinwheel_FiveSixths_WitnessD8_214
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:56:44.848301+00:00
-- url     : https://prove2.me/theorems/a166bbff-2fb0-4306-9db4-4616a60d7b0e
-- title:
--   Exact witness block D8_214
-- statement:
--   These exact witnesses represent words 2567 through 2592 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2567–2592; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_214_2566 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (2))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (7))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_2566
  counts := ![(.branch 16 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 22 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-26)) (.leaf (-27)))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 33 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 36 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 20 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-24))) (.branch 32 (.leaf (-21)) (.leaf (-18)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 24 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_214_2567 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (0))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_2567
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 11 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-26)) (.leaf (-28)))),
  (.branch 10 (.leaf (0)) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 34 (.branch 31 (.leaf (-18)) (.leaf (-16))) (.branch 37 (.leaf (-14)) (.leaf (-7)))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 17 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2568 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (7)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2568
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 37 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.branch 24 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-29))),
  (.branch 28 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 30 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 16 (.branch 12 (.branch 10 (.leaf (-29)) (.branch 11 (.leaf (-28)) (.leaf (-27)))) (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23))))) (.branch 19 (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2569 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (0))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_2569
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 11 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-26)) (.leaf (-28)))),
  (.branch 10 (.leaf (0)) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 31 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-26)))]
  high := ![(.branch 34 (.branch 31 (.leaf (-18)) (.leaf (-16))) (.branch 37 (.leaf (-14)) (.leaf (-7)))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 25 (.leaf (-12)) (.leaf (-11))),
  (.branch 33 (.branch 30 (.branch 17 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-26)) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 16 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21))))) (.branch 21 (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18)))) (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_214_2570 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (4)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (6))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4))))))))
  code := certificateD8_2570
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 5 (.leaf (-14)) (.branch 12 (.leaf (-17)) (.leaf (-18))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 26 (.leaf (-12)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 32 (.leaf (-18)) (.branch 37 (.leaf (-16)) (.leaf (-8)))),
  (.branch 35 (.branch 27 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (-2)),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2571 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2571
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 5 (.leaf (-14)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-15)) (.leaf (-16)))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-6)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-20)) (.leaf (-22)))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 25 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-8)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-14))) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.branch 32 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2572 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (6)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2572
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 31 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-12)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-8)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (-23)) (.leaf (-24)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-17)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 34 (.branch 23 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-14)) (.leaf (-7)))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-21))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 20 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2573 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (5))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (7)) (.leaf (1))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2573
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-28))),
  (.branch 29 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 27 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 24 (.branch 17 (.branch 13 (.branch 11 (.leaf (-28)) (.branch 12 (.leaf (-27)) (.leaf (-26)))) (.branch 15 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2574 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (7)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_2574
  counts := ![(.branch 18 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 23 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 37 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 26 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 28 (.leaf (-12)) (.branch 33 (.leaf (-10)) (.leaf (-8)))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 35 (.branch 34 (.leaf (-10)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.leaf (-31)) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2575 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (7))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2575
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.leaf (7)) (.branch 25 (.leaf (8)) (.leaf (9)))) (.branch 33 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.leaf (13)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 27 (.leaf (-25)) (.leaf (-29)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-8)) (.leaf (-11)))),
  (.branch 23 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 26 (.leaf (0)) (.leaf (-12))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 31 (.branch 28 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-27)) (.branch 37 (.leaf (-26)) (.leaf (-13))))),
  (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 35 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4))))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (-1)),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 24 (.branch 17 (.branch 14 (.branch 12 (.leaf (-27)) (.branch 13 (.leaf (-26)) (.leaf (-25)))) (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_214_2576 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (5)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_2576
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 19 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 33 (.leaf (-17)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_214_2577 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (7)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2577
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 13 (.leaf (-13)) (.branch 32 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-30))),
  (.branch 27 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 33 (.leaf (-16)) (.branch 37 (.leaf (-12)) (.leaf (-7)))),
  (.branch 26 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5))))),
  (.branch 36 (.branch 29 (.leaf (-11)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.leaf (-30)) (.branch 10 (.leaf (-29)) (.leaf (-28)))) (.branch 13 (.branch 12 (.leaf (-27)) (.leaf (-26))) (.branch 14 (.leaf (-25)) (.leaf (-24))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2578 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (7)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2578
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-4)))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 33 (.leaf (-17)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 33 (.branch 19 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-18)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2579 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (7)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2579
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2)))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 26 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 24 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.branch 25 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.leaf (-31)) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2580 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (2))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_2580
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 23 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-28))),
  (.branch 29 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-8)))),
  (.branch 27 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.branch 29 (.leaf (-11)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 17 (.branch 13 (.branch 11 (.leaf (-28)) (.branch 12 (.leaf (-27)) (.leaf (-26)))) (.branch 15 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2581 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (7))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (1))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (7))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2581
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-29)) (.leaf (-31)))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.branch 29 (.branch 16 (.leaf (-31)) (.leaf (-30))) (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-24)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.branch 25 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_214_2582 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (7))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_2582
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 13 (.leaf (-13)) (.branch 32 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 33 (.leaf (-16)) (.branch 37 (.leaf (-12)) (.leaf (-7)))),
  (.branch 29 (.branch 22 (.leaf (-10)) (.leaf (-9))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4))))),
  (.branch 35 (.branch 26 (.leaf (-27)) (.branch 34 (.leaf (-25)) (.leaf (-20)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-5)))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_214_2583 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (7)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (2)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (7)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2583
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 13 (.branch 10 (.leaf (-15)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (-14))) (.branch 25 (.leaf (-15)) (.leaf (-17)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 36 (.leaf (-18)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.branch 26 (.leaf (-17)) (.branch 34 (.leaf (-16)) (.leaf (-13)))) (.branch 36 (.leaf (-10)) (.branch 37 (.leaf (-7)) (.leaf (-4))))),
  (.branch 7 (.leaf (-5)) (.leaf (-4))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 34 (.branch 32 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2584 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (4))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (6))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (5)) (.leaf (7))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (4))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (6)) (.leaf (7))))))))
  code := certificateD8_2584
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 17 (.leaf (-6)) (.branch 32 (.leaf (-7)) (.leaf (-8))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (-23)) (.leaf (-24)))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-21))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0))]
def witnessD8_214_2585 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (5))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_2585
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))) (.branch 29 (.branch 13 (.leaf (-12)) (.leaf (-13))) (.branch 32 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-33))),
  (.branch 24 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 33 (.leaf (-15)) (.branch 37 (.leaf (-12)) (.leaf (-8)))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-33)) (.leaf (-32))) (.branch 8 (.leaf (-31)) (.leaf (-30)))) (.branch 11 (.branch 10 (.leaf (-29)) (.leaf (-28))) (.branch 12 (.leaf (-27)) (.leaf (-26))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.branch 18 (.leaf (-21)) (.leaf (-20))) (.branch 20 (.leaf (-19)) (.leaf (-18)))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 27 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 28 (.leaf (-11)) (.leaf (-10))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2586 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (4))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (7)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (6)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (4))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (1)) (.leaf (7)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (4))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_2586
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 30 (.leaf (-23)) (.leaf (-24)))),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 23 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-24)) (.leaf (-21))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2587 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (3))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (6)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (2))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2587
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-7)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-17)) (.leaf (-19)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 32 (.branch 24 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.branch 26 (.leaf (-27)) (.branch 34 (.leaf (-25)) (.leaf (-20)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-5)))),
  (.branch 37 (.leaf (-12)) (.leaf (-11))),
  (.branch 34 (.branch 20 (.leaf (-19)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2588 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (7))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (4))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2588
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-9)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-26)) (.leaf (-28)))),
  (.branch 10 (.leaf (0)) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-7)))),
  (.branch 33 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 32 (.leaf (-14)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.branch 30 (.branch 17 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_214_2589 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (4))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (7)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (4))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_2589
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-30))),
  (.branch 27 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 36 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.leaf (-30)) (.branch 10 (.leaf (-29)) (.leaf (-28)))) (.branch 13 (.branch 12 (.leaf (-27)) (.leaf (-26))) (.branch 14 (.leaf (-25)) (.leaf (-24))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_214_2590 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (7)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (2))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (5)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (3)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (6)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (2))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (5)) (.leaf (4))))))))
  code := certificateD8_2590
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 14 (.leaf (-5)) (.branch 33 (.leaf (-6)) (.leaf (-7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (-18))) (.branch 34 (.leaf (-19)) (.leaf (-20)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-5)) (.leaf (-8)))),
  (.branch 32 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-25)))]
  high := ![(.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 31 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 29 (.leaf (-11)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-15))) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.leaf (-8)) (.leaf (-7))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 14 (.leaf (-25)) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20))))) (.branch 22 (.branch 20 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-17)))) (.branch 23 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_214_2591 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (4))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (4)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (5))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2591
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-9)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-7)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 28 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-23))),
  (.branch 34 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-7)))),
  (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 32 (.leaf (-14)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_214 : Fin 26 → CycleWitness 8 := ![witnessD8_214_2566, witnessD8_214_2567, witnessD8_214_2568, witnessD8_214_2569, witnessD8_214_2570, witnessD8_214_2571, witnessD8_214_2572, witnessD8_214_2573, witnessD8_214_2574, witnessD8_214_2575, witnessD8_214_2576, witnessD8_214_2577, witnessD8_214_2578, witnessD8_214_2579, witnessD8_214_2580, witnessD8_214_2581, witnessD8_214_2582, witnessD8_214_2583, witnessD8_214_2584, witnessD8_214_2585, witnessD8_214_2586, witnessD8_214_2587, witnessD8_214_2588, witnessD8_214_2589, witnessD8_214_2590, witnessD8_214_2591]
end RealPinwheel.FiveSixths


