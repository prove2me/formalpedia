-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_053
-- name    : RealPinwheel_FiveSixths_WitnessD7_053
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:18.303568+00:00
-- url     : https://prove2.me/theorems/72b0d52d-31a3-46c6-8014-4f61f42545db
-- title:
--   Exact witness block D7_053
-- statement:
--   These exact witnesses represent words 885 through 913 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 885–913; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_053_884 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (5)) (.branch 26 (.leaf (3)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (2)) (.leaf (6)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (5)) (.leaf (1))))))))
  code := certificateD7_884
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-26)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-9))) (.branch 26 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 34 (.branch 29 (.leaf (-7)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 9 (.leaf (-26)) (.branch 31 (.leaf (-25)) (.leaf (-21)))) (.branch 34 (.branch 33 (.leaf (-17)) (.leaf (-13))) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 27 (.leaf (-12)) (.branch 35 (.leaf (-9)) (.leaf (-5)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_885 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (1)) (.leaf (4)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (5))))))))
  code := certificateD7_885
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 29 (.leaf (9)) (.branch 33 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 29 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 34 (.leaf (-5)) (.leaf (-6)))),
  (.branch 21 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 30 (.leaf (-13)) (.branch 34 (.leaf (-11)) (.leaf (-8)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-6)),
  (.branch 24 (.branch 22 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3)))) (.branch 25 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0))))),
  (.branch 31 (.branch 29 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_053_886 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_886
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-18)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 10 (.leaf (-17)) (.branch 31 (.leaf (-18)) (.leaf (-19))))),
  (.branch 23 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-22))),
  (.branch 30 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-18)) (.leaf (-14))))),
  (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 24 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.leaf (-5)) (.leaf (-4))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-22)) (.leaf (-21))) (.branch 16 (.leaf (-20)) (.branch 17 (.leaf (-19)) (.leaf (-18))))) (.branch 21 (.branch 19 (.leaf (-17)) (.branch 20 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.leaf (-14)) (.branch 23 (.leaf (-13)) (.leaf (-12)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-8)) (.leaf (-7))))) (.branch 32 (.branch 30 (.leaf (-6)) (.branch 31 (.leaf (-5)) (.leaf (-4)))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_887 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (4)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_887
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-18)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 10 (.leaf (-17)) (.branch 31 (.leaf (-18)) (.leaf (-19))))),
  (.branch 23 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 29 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-18)) (.leaf (-14))))),
  (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 24 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD7_053_888 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (6))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (5)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_888
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-23)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-23)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-11)) (.leaf (-18)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-34)) (.branch 7 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29))))) (.branch 28 (.branch 22 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 26 (.branch 14 (.branch 8 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-18))) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))),
  (.branch 32 (.branch 30 (.leaf (-18)) (.branch 31 (.leaf (-16)) (.leaf (-14)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-10)) (.leaf (-8))))),
  (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 30 (.branch 27 (.branch 9 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 18 (.leaf (-1)) (.leaf (0)))]
def witnessD7_053_889 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (6))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (6)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (4))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_889
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-23)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-23)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (-5)) (.leaf (-9))))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-34)) (.branch 7 (.leaf (-33)) (.leaf (-32)))) (.branch 13 (.leaf (-31)) (.branch 16 (.leaf (-30)) (.leaf (-29))))) (.branch 28 (.branch 22 (.leaf (-28)) (.branch 25 (.leaf (-27)) (.leaf (-26)))) (.branch 31 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-12)))))),
  (.branch 26 (.branch 14 (.branch 8 (.leaf (-28)) (.leaf (-27))) (.branch 20 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.branch 32 (.leaf (-24)) (.leaf (-18))) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.branch 17 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))),
  (.branch 18 (.branch 9 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 28 (.branch 25 (.branch 5 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 26 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 32 (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7)))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))))]
def witnessD7_053_890 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (0)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_890
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-20)) (.leaf (-33)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 31 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 17 (.leaf (0)) (.leaf (-18))),
  (.branch 30 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.branch 8 (.leaf (-33)) (.leaf (-32))) (.branch 34 (.leaf (-27)) (.leaf (-21)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-18)) (.leaf (-17))) (.branch 20 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-11)) (.leaf (-10)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_891 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.branch 25 (.leaf (0)) (.leaf (2)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (5)) (.branch 34 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_891
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-26)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-20)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0))]
  high := ![(.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 30 (.branch 27 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-21)) (.leaf (-18))))) (.branch 32 (.branch 31 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 31 (.branch 29 (.leaf (-21)) (.branch 30 (.leaf (-18)) (.leaf (-15)))) (.branch 33 (.branch 32 (.leaf (-12)) (.leaf (-9))) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 8 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-9)) (.branch 34 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0))]
def witnessD7_053_892 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (4))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_892
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-26)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.branch 34 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-27))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 21 (.branch 13 (.branch 9 (.leaf (-33)) (.leaf (-32))) (.branch 17 (.leaf (-31)) (.leaf (-30)))) (.branch 29 (.branch 25 (.leaf (-29)) (.leaf (-28))) (.branch 33 (.leaf (-27)) (.branch 34 (.leaf (-18)) (.leaf (-9)))))),
  (.branch 34 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 18 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-3)),
  (.branch 28 (.branch 24 (.branch 5 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-24)))) (.branch 26 (.branch 25 (.leaf (-22)) (.leaf (-20))) (.branch 27 (.leaf (-18)) (.leaf (-16))))) (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-12)) (.leaf (-10)))) (.branch 33 (.branch 32 (.leaf (-8)) (.leaf (-6))) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_053_893 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (5)) (.leaf (1)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (2)) (.branch 34 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_893
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-26)) (.leaf (-30)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 29 (.leaf (-23)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 29 (.branch 21 (.leaf (-30)) (.branch 25 (.leaf (-29)) (.leaf (-28)))) (.branch 33 (.leaf (-27)) (.branch 34 (.leaf (-18)) (.leaf (-9))))),
  (.leaf (-2)),
  (.branch 28 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-6)))),
  (.branch 32 (.branch 30 (.leaf (-24)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.branch 7 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-18))) (.branch 28 (.leaf (-16)) (.branch 29 (.leaf (-14)) (.leaf (-12))))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.branch 19 (.leaf (-1)) (.leaf (0)))))]
def witnessD7_053_894 : CycleWitness 7 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (1)) (.leaf (6)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (3))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_894
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 27 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-23)) (.leaf (-26)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 34 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-19)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-17)) (.leaf (-18))))]
  high := ![(.branch 28 (.leaf (-15)) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 32 (.branch 20 (.leaf (-26)) (.branch 26 (.leaf (-25)) (.leaf (-24)))) (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-12)) (.leaf (-6))))),
  (.branch 23 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 33 (.branch 25 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-7)),
  (.branch 32 (.branch 22 (.leaf (-21)) (.branch 31 (.leaf (-20)) (.leaf (-16)))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-8)) (.leaf (-4))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-16))) (.branch 29 (.leaf (-14)) (.leaf (-12)))) (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_053_895 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 10 (.leaf (3)) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (5)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 27 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_895
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 20 (.leaf (12)) (.branch 22 (.leaf (13)) (.leaf (14))))) (.branch 29 (.branch 26 (.leaf (15)) (.branch 28 (.leaf (16)) (.leaf (17)))) (.branch 31 (.leaf (18)) (.branch 33 (.leaf (19)) (.leaf (20))))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.branch 20 (.leaf (-9)) (.leaf (-11))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-22)) (.leaf (-23)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (-4))) (.branch 32 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 21 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.leaf (-8)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 28 (.branch 16 (.leaf (-23)) (.leaf (-21))) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-6)) (.leaf (-3))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_053_896 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (5)))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.leaf (3)) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_896
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.branch 23 (.leaf (13)) (.leaf (14))))) (.branch 30 (.branch 26 (.leaf (15)) (.branch 28 (.leaf (16)) (.leaf (17)))) (.branch 31 (.leaf (18)) (.branch 33 (.leaf (19)) (.leaf (20))))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 25 (.leaf (-15)) (.branch 32 (.leaf (-13)) (.leaf (-10)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_053_897 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (4)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_897
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_898 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_898
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_053_899 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (5)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_899
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-18))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-9)))),
  (.branch 28 (.branch 24 (.leaf (-3)) (.leaf (-2))) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_053_900 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (1)) (.leaf (5)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_900
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-5)),
  (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.leaf (-4)) (.leaf (-2))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_053_901 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_901
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-16))) (.branch 28 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 32 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_902 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (6))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_902
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_903 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (5)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (4)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (3)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_903
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 25 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-26)) (.branch 10 (.leaf (-25)) (.leaf (-24)))) (.branch 12 (.leaf (-23)) (.branch 13 (.leaf (-22)) (.leaf (-21))))) (.branch 17 (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18)))) (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_053_904 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (5)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (4))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (6)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_904
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-16))) (.branch 28 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 31 (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_053_905 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (5)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.leaf (6)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_905
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-16))) (.branch 28 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-2)),
  (.branch 31 (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_053_906 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (6)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_906
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_053_907 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (4)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (6))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_907
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 20 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_908 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (5)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_908
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-18))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 30 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 22 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_053_909 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (6))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (4)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_909
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 32 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_910 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_910
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_911 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (3)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_911
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 19 (.leaf (-15)) (.branch 21 (.leaf (-16)) (.leaf (-17))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-19))) (.branch 27 (.leaf (-20)) (.leaf (-21)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 22 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-10)))),
  (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_053_912 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_912
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.leaf (-16)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 21 (.leaf (-16)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-18))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.leaf (-7)))),
  (.branch 27 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-16)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_053 : Fin 29 → CycleWitness 7 := ![witnessD7_053_884, witnessD7_053_885, witnessD7_053_886, witnessD7_053_887, witnessD7_053_888, witnessD7_053_889, witnessD7_053_890, witnessD7_053_891, witnessD7_053_892, witnessD7_053_893, witnessD7_053_894, witnessD7_053_895, witnessD7_053_896, witnessD7_053_897, witnessD7_053_898, witnessD7_053_899, witnessD7_053_900, witnessD7_053_901, witnessD7_053_902, witnessD7_053_903, witnessD7_053_904, witnessD7_053_905, witnessD7_053_906, witnessD7_053_907, witnessD7_053_908, witnessD7_053_909, witnessD7_053_910, witnessD7_053_911, witnessD7_053_912]
end RealPinwheel.FiveSixths


