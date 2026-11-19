-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_212
-- name    : RealPinwheel_FiveSixths_WitnessD8_212
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:56:29.537139+00:00
-- url     : https://prove2.me/theorems/d4f9a231-ffe6-44ae-871b-a4efa5f969b7
-- title:
--   Exact witness block D8_212
-- statement:
--   These exact witnesses represent words 2516 through 2540 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2516–2540; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_212_2515 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2515
  counts := ![(.branch 18 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 29 (.branch 23 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 25 (.leaf (11)) (.branch 27 (.leaf (12)) (.leaf (13))))) (.branch 33 (.branch 31 (.leaf (14)) (.leaf (15))) (.branch 36 (.leaf (16)) (.branch 38 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-26))),
  (.branch 26 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 34 (.leaf (-10)) (.leaf (-6))),
  (.branch 36 (.branch 29 (.leaf (-9)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.leaf (-5)) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.branch 19 (.branch 16 (.branch 14 (.leaf (-26)) (.branch 15 (.leaf (-25)) (.leaf (-24)))) (.branch 17 (.leaf (-23)) (.branch 18 (.leaf (-22)) (.leaf (-21))))) (.branch 22 (.branch 20 (.leaf (-20)) (.branch 21 (.leaf (-19)) (.leaf (-18)))) (.branch 24 (.branch 23 (.leaf (-17)) (.leaf (-16))) (.branch 25 (.leaf (-15)) (.leaf (-14)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-13)) (.branch 28 (.leaf (-12)) (.leaf (-11)))) (.branch 30 (.leaf (-10)) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-13)) (.branch 28 (.leaf (-12)) (.leaf (-11)))) (.branch 30 (.leaf (-10)) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_212_2516 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (2))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2516
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 34 (.branch 31 (.leaf (11)) (.leaf (12))) (.branch 37 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 14 (.leaf (-22)) (.branch 16 (.leaf (-26)) (.leaf (-33))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 30 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 36 (.leaf (-10)) (.leaf (-12)))),
  (.branch 29 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-24))),
  (.branch 35 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 20 (.branch 17 (.leaf (-33)) (.leaf (-32))) (.branch 23 (.leaf (-31)) (.leaf (-30)))) (.branch 32 (.branch 29 (.leaf (-29)) (.leaf (-28))) (.branch 35 (.leaf (-27)) (.branch 38 (.leaf (-26)) (.leaf (-18)))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-9)) (.leaf (-6)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 28 (.branch 6 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 16 (.leaf (-24)) (.branch 17 (.leaf (-23)) (.leaf (-22)))) (.branch 19 (.leaf (-21)) (.branch 20 (.leaf (-20)) (.leaf (-19))))) (.branch 24 (.branch 22 (.leaf (-18)) (.branch 23 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-11)) (.leaf (-10)))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_212_2517 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (3))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (6)) (.leaf (2))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2517
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 34 (.branch 31 (.leaf (11)) (.leaf (12))) (.branch 37 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 14 (.leaf (-22)) (.branch 16 (.leaf (-26)) (.leaf (-33))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 30 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 36 (.leaf (-10)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 26 (.branch 20 (.branch 17 (.leaf (-33)) (.leaf (-32))) (.branch 23 (.leaf (-31)) (.leaf (-30)))) (.branch 32 (.branch 29 (.leaf (-29)) (.leaf (-28))) (.branch 35 (.leaf (-27)) (.branch 38 (.leaf (-26)) (.leaf (-18)))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-9)) (.leaf (-6)))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-18))) (.branch 32 (.leaf (-16)) (.branch 33 (.leaf (-14)) (.leaf (-12))))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 36 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 28 (.branch 6 (.leaf (-15)) (.branch 27 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 31 (.leaf (-10)) (.leaf (-9))))) (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_212_2518 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (3))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (5))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (2))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (7))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (5))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_2518
  counts := ![(.branch 16 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 16 (.leaf (-7)) (.branch 29 (.leaf (-9)) (.leaf (-11))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-25)) (.leaf (-26)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 26 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-30))))]
  high := ![(.branch 36 (.branch 30 (.leaf (-11)) (.leaf (-10))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7))))),
  (.branch 31 (.branch 14 (.leaf (-26)) (.leaf (-24))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-14)) (.leaf (-7))))),
  (.branch 27 (.leaf (-13)) (.branch 33 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 32 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 33 (.leaf (-14)) (.leaf (-12)))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 38 (.leaf (-4)) (.leaf (-2))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-28)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-22))) (.branch 30 (.leaf (-20)) (.leaf (-18))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-14))) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_212_2519 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (3)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (7)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (5))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (6)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (7))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_2519
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 21 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.leaf (15)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 31 (.leaf (-31)) (.leaf (-32)))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.leaf (-12)) (.branch 38 (.leaf (-10)) (.leaf (-5)))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-32)) (.leaf (-28))) (.branch 34 (.leaf (-24)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 26 (.branch 6 (.leaf (-19)) (.branch 16 (.leaf (-18)) (.leaf (-17)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 19 (.leaf (-6)) (.branch 29 (.leaf (-5)) (.leaf (-4)))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_212_2520 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (7))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (6))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (5))))))))
  code := certificateD8_2520
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-10)) (.branch 30 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-23)) (.leaf (-29)))),
  (.branch 3 (.leaf (0)) (.branch 37 (.leaf (-15)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (-14)) (.leaf (-16))))]
  high := ![(.branch 36 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-7)) (.leaf (-5))))),
  (.branch 27 (.branch 17 (.branch 12 (.leaf (-29)) (.leaf (-28))) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 37 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 38 (.leaf (-16)) (.leaf (-8))))),
  (.branch 38 (.leaf (-16)) (.leaf (-8))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-18))) (.branch 32 (.leaf (-16)) (.branch 33 (.leaf (-14)) (.leaf (-12))))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0)),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_212_2521 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (5))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (7)) (.leaf (1))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (5))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_2521
  counts := ![(.branch 19 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.leaf (15)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0))]
  high := ![(.branch 33 (.leaf (-9)) (.branch 36 (.leaf (-7)) (.leaf (-5)))),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 14 (.branch 4 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-16))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 27 (.branch 17 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-18))) (.branch 32 (.leaf (-16)) (.branch 33 (.leaf (-14)) (.leaf (-12))))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessD8_212_2522 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (0))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (7)) (.leaf (2))))))))
  code := certificateD8_2522
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 25 (.leaf (0)) (.leaf (-14))),
  (.branch 38 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 33 (.leaf (-8)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-2)) (.leaf (0)))),
  (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-27)) (.branch 14 (.leaf (-26)) (.leaf (-25)))) (.branch 16 (.leaf (-24)) (.branch 17 (.leaf (-23)) (.leaf (-22))))) (.branch 21 (.branch 19 (.leaf (-21)) (.branch 20 (.leaf (-20)) (.leaf (-19)))) (.branch 23 (.branch 22 (.leaf (-18)) (.leaf (-17))) (.branch 24 (.leaf (-16)) (.leaf (-15)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_212_2523 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (7))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (7)) (.leaf (0))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (5)) (.leaf (3))))))))
  code := certificateD8_2523
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))) (.branch 23 (.leaf (-10)) (.branch 36 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-27)) (.leaf (-29)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-9)) (.leaf (-6)))),
  (.branch 29 (.leaf (-7)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 33 (.branch 23 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-24)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 20 (.branch 10 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 32 (.branch 28 (.branch 7 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-24)))) (.branch 30 (.branch 29 (.leaf (-22)) (.leaf (-20))) (.branch 31 (.leaf (-18)) (.leaf (-16))))) (.branch 35 (.branch 33 (.leaf (-14)) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2))))]
def witnessD8_212_2524 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (6)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (5))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2524
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 29 (.branch 23 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10)))) (.branch 35 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 38 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 14 (.leaf (-19)) (.leaf (-26)))),
  (.branch 28 (.branch 2 (.leaf (0)) (.leaf (-14))) (.branch 34 (.leaf (-16)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 24 (.branch 18 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 21 (.leaf (-24)) (.leaf (-23)))) (.branch 30 (.branch 27 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-20)) (.branch 36 (.leaf (-19)) (.leaf (-18)))))),
  (.branch 36 (.branch 35 (.leaf (-18)) (.leaf (-15))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-9)) (.leaf (-6))))),
  (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 37 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-22)) (.leaf (-20)))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-16)) (.leaf (-14))))) (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 38 (.leaf (-4)) (.leaf (-2)))]
def witnessD8_212_2525 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (7))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (6))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (7))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2525
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-31)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-30)))),
  (.branch 14 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 36 (.branch 26 (.leaf (-34)) (.branch 31 (.leaf (-33)) (.leaf (-32)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-16)) (.leaf (-8))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 38 (.leaf (-14)) (.leaf (-7)))),
  (.branch 37 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-28)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-22))) (.branch 30 (.leaf (-20)) (.leaf (-18))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-14))) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 36 (.branch 15 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_212_2526 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (6)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (6)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (3))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (7)) (.leaf (3))))))))
  code := certificateD8_2526
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 20 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-24)) (.leaf (-26)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 33 (.leaf (-23)) (.leaf (-24)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-23))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 33 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.branch 37 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.branch 36 (.branch 27 (.leaf (-26)) (.branch 35 (.leaf (-25)) (.leaf (-20)))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.branch 8 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0))))),
  (.branch 36 (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-20)) (.leaf (-16)))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 30 (.branch 9 (.leaf (-23)) (.branch 29 (.leaf (-22)) (.leaf (-20)))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-16)) (.leaf (-14))))) (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 19 (.leaf (-3)) (.leaf (-2)))]
def witnessD8_212_2527 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_2527
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-18)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 18 (.leaf (0)) (.leaf (-21))),
  (.branch 37 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 25 (.branch 17 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 33 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))))),
  (.leaf (-2)),
  (.branch 36 (.branch 16 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-13)) (.leaf (-8))))),
  (.branch 34 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-22)) (.leaf (-20)))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-16)) (.leaf (-14))))) (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-21)) (.leaf (-20))) (.branch 21 (.leaf (-19)) (.branch 22 (.leaf (-18)) (.leaf (-17))))) (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_212_2528 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (7))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (2))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (7))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (4)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_2528
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-27)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-23)) (.leaf (-25)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 33 (.branch 25 (.leaf (-33)) (.branch 29 (.leaf (-32)) (.leaf (-31)))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10))))),
  (.branch 36 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-9)) (.leaf (-6))))),
  (.branch 35 (.branch 19 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-15))) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 35 (.branch 24 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_212_2529 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (4)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (3))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 25 (.leaf (7)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (6)) (.leaf (4))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (7)) (.leaf (4))))))))
  code := certificateD8_2529
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 39 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 28 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 29 (.leaf (-9)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 19 (.leaf (-27)) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-15))) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.branch 6 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.leaf (-11)) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_212_2530 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (7)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (5)) (.leaf (3))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (1)) (.leaf (7)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (6)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (5))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2530
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-31)) (.leaf (-35)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-22)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 31 (.branch 21 (.leaf (-35)) (.branch 26 (.leaf (-34)) (.leaf (-33)))) (.branch 37 (.branch 36 (.leaf (-32)) (.leaf (-24))) (.branch 38 (.leaf (-16)) (.leaf (-8))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.leaf (-14)) (.branch 38 (.leaf (-13)) (.leaf (-9)))),
  (.branch 35 (.branch 15 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6))))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_212_2531 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (7))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (5))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (4))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (6)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (5))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (4))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (7))))))))
  code := certificateD8_2531
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 32 (.leaf (-27)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 34 (.leaf (-11)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 36 (.branch 29 (.leaf (-9)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.branch 33 (.leaf (-28)) (.branch 34 (.leaf (-24)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.branch 7 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-18))) (.branch 32 (.leaf (-16)) (.branch 33 (.leaf (-14)) (.leaf (-12))))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 20 (.leaf (-1)) (.leaf (0)))]
def witnessD8_212_2532 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (5)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (7)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (4))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2532
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 36 (.leaf (-29)) (.leaf (-30)))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 35 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-24)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-32))),
  (.branch 28 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))),
  (.branch 37 (.branch 36 (.leaf (-14)) (.leaf (-11))) (.branch 38 (.leaf (-8)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 35 (.branch 19 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-15))) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-2)),
  (.branch 24 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-5)))),
  (.branch 23 (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-32)) (.leaf (-31))) (.branch 10 (.leaf (-30)) (.leaf (-29)))) (.branch 13 (.branch 12 (.leaf (-28)) (.leaf (-27))) (.branch 14 (.leaf (-26)) (.leaf (-25))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-24)) (.leaf (-23))) (.branch 18 (.leaf (-22)) (.leaf (-21)))) (.branch 21 (.branch 20 (.leaf (-20)) (.leaf (-19))) (.branch 22 (.leaf (-18)) (.leaf (-17)))))) (.branch 31 (.branch 27 (.branch 25 (.branch 24 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 30 (.leaf (-10)) (.leaf (-9))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_212_2533 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (6)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (7)) (.leaf (1))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (6))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (7)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_2533
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-27)) (.leaf (-30)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-15)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 37 (.branch 32 (.leaf (-11)) (.leaf (-9))) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.leaf (-5)) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 23 (.branch 13 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-24)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-16))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 36 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_212_2534 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (7))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (2))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (7))))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (5))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (6))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (4)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (1))) (.branch 37 (.leaf (7)) (.branch 38 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2534
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-32))) (.branch 17 (.leaf (-36)) (.branch 28 (.leaf (-37)) (.leaf (-38))))),
  (.branch 2 (.leaf (0)) (.leaf (-25))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 36 (.branch 29 (.leaf (-38)) (.branch 35 (.leaf (-35)) (.leaf (-28)))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-14)) (.leaf (-7))))),
  (.branch 31 (.branch 3 (.leaf (-25)) (.leaf (-24))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-14)) (.leaf (-7))))),
  (.branch 16 (.leaf (-12)) (.branch 33 (.leaf (-10)) (.leaf (-7)))),
  (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 35 (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_212_2535 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (2))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (7)) (.leaf (0))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (4)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (2)) (.leaf (6))))) (.branch 36 (.branch 35 (.leaf (3)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2535
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 18 (.leaf (-12)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-9)))),
  (.branch 29 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 35 (.leaf (-13)) (.leaf (-15)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 32 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2)))),
  (.branch 31 (.branch 19 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 37 (.leaf (-11)) (.branch 38 (.leaf (-8)) (.leaf (-5))))),
  (.branch 28 (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7)))) (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-2)) (.leaf (0))))),
  (.branch 37 (.branch 36 (.leaf (-15)) (.leaf (-12))) (.branch 38 (.leaf (-9)) (.leaf (-6)))),
  (.branch 29 (.leaf (-5)) (.leaf (-4))),
  (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 36 (.branch 15 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))),
  (.branch 31 (.branch 27 (.branch 5 (.leaf (-16)) (.branch 26 (.leaf (-15)) (.leaf (-14)))) (.branch 29 (.branch 28 (.leaf (-13)) (.leaf (-12))) (.branch 30 (.leaf (-11)) (.leaf (-10))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-9)) (.leaf (-8))) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 37 (.branch 36 (.leaf (-5)) (.leaf (-4))) (.branch 38 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_212_2536 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (6))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (7))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_2536
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-33))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-23))),
  (.branch 36 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-6)))),
  (.branch 29 (.leaf (-7)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 4 (.leaf (-33)) (.leaf (-32))) (.branch 25 (.leaf (-30)) (.leaf (-28)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-24))) (.branch 29 (.leaf (-22)) (.leaf (-20))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-16))) (.branch 33 (.leaf (-14)) (.leaf (-12)))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-18))) (.branch 32 (.leaf (-16)) (.branch 33 (.leaf (-14)) (.leaf (-12))))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-23)) (.leaf (-22))) (.branch 19 (.leaf (-21)) (.branch 20 (.leaf (-20)) (.leaf (-19))))) (.branch 24 (.branch 22 (.leaf (-18)) (.branch 23 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))))) (.branch 33 (.branch 30 (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-11)) (.leaf (-10)))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_212_2537 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (7))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (7)) (.branch 28 (.leaf (5)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (6)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (5)) (.leaf (7))))))))
  code := certificateD8_2537
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-31))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-15))) (.branch 23 (.leaf (-21)) (.leaf (-23)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-19)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-27)) (.leaf (-29)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 22 (.branch 7 (.branch 2 (.leaf (-31)) (.leaf (-30))) (.branch 12 (.leaf (-29)) (.branch 17 (.leaf (-28)) (.leaf (-27))))) (.branch 32 (.branch 27 (.leaf (-26)) (.leaf (-25))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 36 (.branch 24 (.leaf (-23)) (.branch 30 (.leaf (-22)) (.leaf (-21)))) (.branch 37 (.leaf (-17)) (.branch 38 (.leaf (-13)) (.leaf (-9))))),
  (.branch 31 (.branch 11 (.leaf (-6)) (.leaf (-5))) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-16))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 35 (.branch 33 (.branch 23 (.leaf (-29)) (.leaf (-28))) (.branch 34 (.leaf (-24)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 29 (.leaf (-5)) (.leaf (-4))),
  (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_212_2538 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (7))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (6))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (5))) (.branch 27 (.leaf (3)) (.branch 28 (.leaf (0)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (7)) (.leaf (2))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (0)) (.leaf (6))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2538
  counts := ![(.branch 19 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 36 (.leaf (-24)) (.leaf (-27)))),
  (.branch 2 (.leaf (0)) (.branch 23 (.leaf (-23)) (.leaf (-37)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-27)) (.leaf (-30)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-22))))]
  high := ![(.branch 37 (.leaf (-27)) (.branch 38 (.leaf (-20)) (.leaf (-13)))),
  (.branch 36 (.branch 24 (.leaf (-37)) (.branch 30 (.leaf (-36)) (.leaf (-35)))) (.branch 37 (.leaf (-29)) (.branch 38 (.leaf (-23)) (.leaf (-17))))),
  (.branch 5 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6)))),
  (.branch 18 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 34 (.branch 23 (.branch 13 (.leaf (-30)) (.leaf (-29))) (.branch 33 (.leaf (-28)) (.leaf (-24)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-16))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-8)) (.leaf (-4)))))),
  (.leaf (0)),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-17)) (.leaf (-15))))) (.branch 36 (.branch 35 (.leaf (-13)) (.leaf (-11))) (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-7)) (.leaf (-5))))))]
def witnessD8_212_2539 : CycleWitness 8 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (7))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (6)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (7))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (0)) (.leaf (4)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (7)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (5)) (.leaf (0))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (6))))))))
  code := certificateD8_2539
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-10)) (.leaf (-11)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 25 (.branch 17 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 33 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))))),
  (.leaf (-2)),
  (.branch 28 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 30 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 36 (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-5)) (.leaf (-4)))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))))]
def witnessD8_212 : Fin 25 → CycleWitness 8 := ![witnessD8_212_2515, witnessD8_212_2516, witnessD8_212_2517, witnessD8_212_2518, witnessD8_212_2519, witnessD8_212_2520, witnessD8_212_2521, witnessD8_212_2522, witnessD8_212_2523, witnessD8_212_2524, witnessD8_212_2525, witnessD8_212_2526, witnessD8_212_2527, witnessD8_212_2528, witnessD8_212_2529, witnessD8_212_2530, witnessD8_212_2531, witnessD8_212_2532, witnessD8_212_2533, witnessD8_212_2534, witnessD8_212_2535, witnessD8_212_2536, witnessD8_212_2537, witnessD8_212_2538, witnessD8_212_2539]
end RealPinwheel.FiveSixths


