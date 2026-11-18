-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_051
-- name    : RealPinwheel_FiveSixths_WitnessD7_051
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:19.775007+00:00
-- url     : https://prove2.me/theorems/5ba03cd6-2518-48c3-be95-5561a4a44f01
-- title:
--   Exact witness block D7_051
-- statement:
--   These exact witnesses represent words 831 through 857 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 831–857; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_051_830 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_830
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-15)))),
  (.leaf (0)),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (-3)) (.leaf (-5)))),
  (.branch 23 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 22 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 19 (.leaf (-15)) (.leaf (-13))) (.branch 35 (.leaf (-9)) (.leaf (-5)))),
  (.leaf (0)),
  (.leaf (-5)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_051_831 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (6)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (5)) (.leaf (2))))))))
  code := certificateD7_831
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-5)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 33 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_832 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_832
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 23 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 34 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_833 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (6)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_833
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-28))),
  (.branch 26 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.leaf (-5)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 33 (.branch 23 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 15 (.branch 11 (.branch 9 (.leaf (-28)) (.branch 10 (.leaf (-27)) (.leaf (-26)))) (.branch 13 (.branch 12 (.leaf (-25)) (.leaf (-24))) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_834 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_834
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 22 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_835 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (2)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_835
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 33 (.leaf (-12)) (.leaf (-13)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 20 (.leaf (-3)) (.branch 30 (.leaf (-4)) (.leaf (-6))))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-3)) (.leaf (0)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_836 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (0))) (.branch 26 (.leaf (1)) (.leaf (3))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_836
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 24 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_837 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_837
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 24 (.leaf (0)) (.leaf (-12))),
  (.branch 33 (.leaf (0)) (.leaf (-3))),
  (.branch 15 (.leaf (0)) (.leaf (-21)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_051_838 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (5)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_838
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_051_839 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (6))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD7_839
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-21))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_051_840 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_840
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 24 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 24 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_841 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (6))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_841
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 21 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 34 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 33 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_842 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_842
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 18 (.leaf (0)) (.leaf (-18))),
  (.leaf (0))]
  high := ![(.branch 34 (.branch 30 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 35 (.leaf (-4)) (.leaf (-2))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_051_843 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (6))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_843
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 34 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 26 (.leaf (-5)) (.branch 27 (.leaf (-4)) (.leaf (-3)))) (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 12 (.leaf (-25)) (.branch 13 (.leaf (-24)) (.leaf (-23)))) (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20))))) (.branch 20 (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17)))) (.branch 21 (.leaf (-16)) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_844 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (2)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_844
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-10)) (.branch 25 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (-3))) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-26))),
  (.branch 28 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 30 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 7 (.leaf (-18)) (.leaf (-17))),
  (.branch 31 (.branch 25 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-2)) (.leaf (0))))),
  (.branch 6 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 23 (.branch 16 (.branch 13 (.branch 11 (.leaf (-26)) (.branch 12 (.leaf (-25)) (.leaf (-24)))) (.branch 14 (.leaf (-23)) (.branch 15 (.leaf (-22)) (.leaf (-21))))) (.branch 19 (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18)))) (.branch 21 (.branch 20 (.leaf (-17)) (.leaf (-16))) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_845 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (6)) (.leaf (0))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (2)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_845
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 18 (.leaf (-10)) (.branch 25 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.branch 19 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-12)) (.leaf (-15)))),
  (.branch 17 (.leaf (0)) (.branch 32 (.leaf (-3)) (.leaf (-8))))]
  high := ![(.branch 30 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 7 (.leaf (-18)) (.leaf (-17))),
  (.branch 31 (.branch 25 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-2)) (.leaf (0))))),
  (.branch 6 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10))))) (.branch 32 (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7)))) (.branch 34 (.branch 33 (.leaf (-6)) (.leaf (-5))) (.branch 35 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5))))]
def witnessD7_051_846 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (0))) (.branch 30 (.leaf (3)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_846
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-26))),
  (.branch 28 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.branch 16 (.branch 13 (.branch 11 (.leaf (-26)) (.branch 12 (.leaf (-25)) (.leaf (-24)))) (.branch 14 (.leaf (-23)) (.branch 15 (.leaf (-22)) (.leaf (-21))))) (.branch 19 (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18)))) (.branch 21 (.branch 20 (.leaf (-17)) (.leaf (-16))) (.branch 22 (.leaf (-15)) (.leaf (-14)))))) (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_847 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_847
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_051_848 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (4))) (.branch 30 (.leaf (1)) (.leaf (6)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_848
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_849 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_849
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-9)) (.branch 28 (.leaf (-10)) (.leaf (-12))))),
  (.branch 10 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 34 (.branch 30 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.leaf (-7)))),
  (.branch 29 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 32 (.leaf (-3)) (.leaf (0))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_051_850 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_850
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-9)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 23 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-9)) (.branch 32 (.leaf (-7)) (.leaf (-5)))),
  (.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_851 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (3)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_851
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_051_852 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (4)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (6)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_852
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-13)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 25 (.leaf (-16)) (.leaf (-14))) (.branch 34 (.leaf (-11)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 22 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_853 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (3))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (3)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_853
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 23 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 32 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-5)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_051_854 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (4))) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_854
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 28 (.leaf (-18)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 34 (.branch 30 (.leaf (-17)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.leaf (-7)))),
  (.branch 29 (.leaf (-28)) (.branch 35 (.leaf (-26)) (.leaf (-23)))),
  (.branch 33 (.branch 19 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_051_855 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (5))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (6))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_855
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 17 (.leaf (-22)) (.branch 24 (.leaf (-23)) (.leaf (-24))))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 27 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-5))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 25 (.leaf (-24)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_051_856 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (6)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (4)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (5)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_856
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-6))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.leaf (-5)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_051 : Fin 27 → CycleWitness 7 := ![witnessD7_051_830, witnessD7_051_831, witnessD7_051_832, witnessD7_051_833, witnessD7_051_834, witnessD7_051_835, witnessD7_051_836, witnessD7_051_837, witnessD7_051_838, witnessD7_051_839, witnessD7_051_840, witnessD7_051_841, witnessD7_051_842, witnessD7_051_843, witnessD7_051_844, witnessD7_051_845, witnessD7_051_846, witnessD7_051_847, witnessD7_051_848, witnessD7_051_849, witnessD7_051_850, witnessD7_051_851, witnessD7_051_852, witnessD7_051_853, witnessD7_051_854, witnessD7_051_855, witnessD7_051_856]
end RealPinwheel.FiveSixths


