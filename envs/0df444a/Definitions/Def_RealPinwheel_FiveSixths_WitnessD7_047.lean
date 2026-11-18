-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_047
-- name    : RealPinwheel_FiveSixths_WitnessD7_047
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:37.014258+00:00
-- url     : https://prove2.me/theorems/2e2588c7-4281-49c4-8f5c-213e41b02523
-- title:
--   Exact witness block D7_047
-- statement:
--   These exact witnesses represent words 725 through 750 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 725–750; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_047_724 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (6)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (6)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (5)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_724
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 25 (.leaf (-31)) (.leaf (-34)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-22)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0))]
  high := ![(.branch 36 (.branch 26 (.leaf (-34)) (.branch 31 (.leaf (-33)) (.leaf (-32)))) (.branch 37 (.leaf (-24)) (.branch 38 (.leaf (-16)) (.leaf (-8))))),
  (.branch 33 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 38 (.leaf (-14)) (.leaf (-7)))),
  (.branch 37 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))),
  (.branch 35 (.branch 15 (.leaf (-22)) (.branch 25 (.leaf (-21)) (.leaf (-20)))) (.branch 37 (.branch 36 (.leaf (-16)) (.leaf (-12))) (.branch 38 (.leaf (-8)) (.leaf (-4))))),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_047_725 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (1)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (4)) (.leaf (1))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_725
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-29))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))) (.branch 18 (.branch 14 (.leaf (-7)) (.leaf (-8))) (.branch 31 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-24)) (.leaf (-25)))),
  (.branch 22 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-6)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.branch 6 (.branch 2 (.leaf (-29)) (.leaf (-28))) (.branch 10 (.leaf (-27)) (.branch 14 (.leaf (-26)) (.leaf (-25))))) (.branch 30 (.branch 22 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 34 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 37 (.branch 32 (.leaf (-10)) (.leaf (-9))) (.branch 38 (.leaf (-7)) (.leaf (-5)))),
  (.branch 36 (.branch 35 (.leaf (-25)) (.leaf (-20))) (.branch 37 (.leaf (-15)) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-2)),
  (.branch 36 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2))))),
  (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-1)) (.leaf (0)))]
def witnessD7_047_726 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (0)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_726
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-18)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (-1)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-23)) (.leaf (-24)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 25 (.branch 17 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 33 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))))),
  (.leaf (-2)),
  (.branch 36 (.branch 16 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-13)) (.leaf (-8))))),
  (.branch 34 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 30 (.branch 28 (.leaf (-24)) (.branch 29 (.leaf (-22)) (.leaf (-20)))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-16)) (.leaf (-14))))) (.branch 36 (.branch 34 (.leaf (-12)) (.branch 35 (.leaf (-10)) (.leaf (-8)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 38 (.leaf (-4)) (.leaf (-2)))]
def witnessD7_047_727 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (6))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (1))) (.branch 27 (.leaf (3)) (.branch 28 (.leaf (0)) (.leaf (2)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (6)) (.leaf (1))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (0))) (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_727
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 26 (.leaf (6)) (.leaf (7)))) (.branch 34 (.leaf (8)) (.branch 38 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-29)) (.leaf (-36)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-18)) (.leaf (-24)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 33 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 25 (.branch 17 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 21 (.leaf (-34)) (.leaf (-33)))) (.branch 33 (.branch 29 (.leaf (-32)) (.leaf (-31))) (.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))))),
  (.leaf (-2)),
  (.branch 36 (.branch 16 (.leaf (-24)) (.leaf (-23))) (.branch 37 (.leaf (-18)) (.branch 38 (.leaf (-13)) (.leaf (-8))))),
  (.branch 28 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-8))) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 36 (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7)))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))))]
def witnessD7_047_728 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (3))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (0)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (2))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_728
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-24))) (.branch 31 (.leaf (-27)) (.branch 35 (.leaf (-31)) (.leaf (-34))))),
  (.branch 2 (.leaf (0)) (.leaf (-23))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-32)))),
  (.branch 6 (.leaf (0)) (.branch 38 (.leaf (-2)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 37 (.branch 36 (.leaf (-34)) (.leaf (-27))) (.branch 38 (.leaf (-20)) (.leaf (-13)))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (-23)) (.leaf (-22))) (.branch 13 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.branch 23 (.leaf (-19)) (.leaf (-18))) (.branch 33 (.leaf (-17)) (.branch 38 (.leaf (-16)) (.leaf (-8)))))),
  (.branch 31 (.branch 19 (.leaf (-32)) (.branch 25 (.leaf (-31)) (.leaf (-30)))) (.branch 37 (.leaf (-29)) (.branch 38 (.leaf (-23)) (.leaf (-17))))),
  (.leaf (-6)),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6))))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-2)) (.leaf (0))))]
def witnessD7_047_729 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (3)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_729
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 25 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 33 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.leaf (15)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (-29)) (.leaf (-30)))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 28 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-5)))),
  (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6))))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-30)) (.branch 26 (.leaf (-28)) (.leaf (-26)))) (.branch 29 (.branch 28 (.leaf (-24)) (.leaf (-22))) (.branch 30 (.leaf (-20)) (.leaf (-18))))) (.branch 35 (.branch 33 (.branch 32 (.leaf (-16)) (.leaf (-14))) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 37 (.branch 36 (.leaf (-8)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 34 (.branch 32 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 33 (.leaf (-14)) (.leaf (-12)))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 38 (.leaf (-4)) (.leaf (-2)))]
def witnessD7_047_730 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (5)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (3))) (.branch 27 (.leaf (2)) (.branch 28 (.leaf (6)) (.leaf (0)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (4))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (3))))) (.branch 36 (.branch 35 (.leaf (1)) (.leaf (0))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_730
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 36 (.leaf (-29)) (.leaf (-30)))),
  (.branch 24 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 35 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-24)) (.leaf (-28)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 37 (.leaf (-30)) (.branch 38 (.leaf (-20)) (.leaf (-10)))),
  (.branch 37 (.branch 36 (.leaf (-14)) (.leaf (-11))) (.branch 38 (.leaf (-8)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 35 (.branch 19 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 27 (.leaf (-26)) (.leaf (-25)))) (.branch 37 (.branch 36 (.leaf (-20)) (.leaf (-15))) (.branch 38 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-2)),
  (.branch 24 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-5)))),
  (.branch 33 (.branch 30 (.branch 8 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8))))) (.branch 36 (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.leaf (-4)) (.branch 38 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_047_731 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (6))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (5)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 36 (.branch 35 (.leaf (2)) (.leaf (6))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_731
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-33))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (-19)) (.leaf (-20)))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-6)))),
  (.branch 29 (.leaf (-7)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 4 (.leaf (-33)) (.leaf (-32))) (.branch 25 (.leaf (-30)) (.leaf (-28)))) (.branch 28 (.branch 27 (.leaf (-26)) (.leaf (-24))) (.branch 29 (.leaf (-22)) (.leaf (-20))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-16))) (.branch 33 (.leaf (-14)) (.leaf (-12)))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 34 (.branch 31 (.branch 30 (.leaf (-20)) (.leaf (-18))) (.branch 32 (.leaf (-16)) (.branch 33 (.leaf (-14)) (.leaf (-12))))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 37 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 38 (.leaf (-4)) (.leaf (-2))))]
def witnessD7_047_732 : CycleWitness 7 where
  length := 39
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (2))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (3)) (.leaf (1)))))) (.branch 34 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (1)) (.leaf (2))))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (3))) (.branch 37 (.leaf (1)) (.branch 38 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_732
  counts := ![(.branch 18 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 24 (.leaf (5)) (.leaf (6))) (.branch 33 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 21 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 26 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 36 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 12 (.leaf (0)) (.leaf (-27))),
  (.branch 25 (.leaf (0)) (.leaf (-14))),
  (.branch 38 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 36 (.leaf (-12)) (.leaf (-9))) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.leaf (-6)) (.leaf (-3))),
  (.branch 35 (.leaf (-2)) (.leaf (0))),
  (.branch 37 (.leaf (-9)) (.branch 38 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-27)) (.branch 14 (.leaf (-26)) (.leaf (-25)))) (.branch 16 (.leaf (-24)) (.branch 17 (.leaf (-23)) (.leaf (-22))))) (.branch 21 (.branch 19 (.leaf (-21)) (.branch 20 (.leaf (-20)) (.leaf (-19)))) (.branch 23 (.branch 22 (.leaf (-18)) (.leaf (-17))) (.branch 24 (.leaf (-16)) (.leaf (-15)))))) (.branch 32 (.branch 28 (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 28 (.branch 26 (.leaf (-14)) (.branch 27 (.leaf (-13)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 37 (.branch 36 (.leaf (-4)) (.leaf (-3))) (.branch 38 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_047_733 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 6 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.leaf (1))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.leaf (3)))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (1))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_733
  counts := ![(.branch 18 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 16 (.leaf (9)) (.leaf (10)))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (11)) (.branch 21 (.leaf (12)) (.leaf (13)))) (.branch 24 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16))))) (.branch 33 (.branch 30 (.leaf (17)) (.branch 31 (.leaf (18)) (.leaf (19)))) (.branch 35 (.leaf (20)) (.branch 37 (.leaf (21)) (.leaf (22))))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 3 (.leaf (-14)) (.branch 22 (.leaf (-21)) (.leaf (-26))))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-7)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 13 (.leaf (0)) (.leaf (-25))),
  (.branch 25 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 34 (.leaf (-23)) (.branch 36 (.leaf (-21)) (.leaf (-19))))),
  (.branch 30 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 14 (.leaf (-25)) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20))))) (.branch 22 (.branch 20 (.leaf (-19)) (.branch 21 (.leaf (-18)) (.leaf (-17)))) (.branch 23 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_047_734 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 8 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 9 (.leaf (1)) (.leaf (0))))) (.branch 14 (.branch 11 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (0)) (.leaf (1)))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (0)))) (.branch 27 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (0))))) (.branch 33 (.branch 30 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 36 (.branch 35 (.leaf (0)) (.leaf (6))) (.branch 37 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_734
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 15 (.leaf (9)) (.branch 16 (.leaf (10)) (.leaf (11)))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (12)) (.branch 21 (.leaf (13)) (.leaf (14)))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))) (.branch 32 (.branch 29 (.leaf (18)) (.branch 31 (.leaf (19)) (.leaf (20)))) (.branch 35 (.branch 34 (.leaf (21)) (.leaf (22))) (.branch 37 (.leaf (23)) (.leaf (24))))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 3 (.leaf (-6)) (.branch 22 (.leaf (-9)) (.leaf (-10))))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 11 (.leaf (0)) (.leaf (-27))),
  (.branch 23 (.leaf (0)) (.leaf (-15))),
  (.branch 36 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 23 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-7)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 33 (.branch 18 (.branch 5 (.leaf (-26)) (.leaf (-25))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 24 (.branch 17 (.branch 14 (.branch 12 (.leaf (-27)) (.branch 13 (.leaf (-26)) (.leaf (-25)))) (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_047_735 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (4)) (.branch 28 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_735
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 28 (.branch 21 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13))))) (.branch 32 (.branch 30 (.leaf (14)) (.leaf (15))) (.branch 34 (.leaf (16)) (.branch 36 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 5 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 22 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))) (.branch 21 (.leaf (-17)) (.branch 23 (.leaf (-18)) (.leaf (-19))))),
  (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-22))),
  (.branch 35 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.leaf (-19)) (.branch 37 (.leaf (-18)) (.leaf (-11)))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18))))) (.branch 24 (.branch 22 (.leaf (-17)) (.branch 23 (.leaf (-16)) (.leaf (-15)))) (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_047_736 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.leaf (5))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0)))) (.branch 27 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (0))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (4)) (.leaf (0))) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_736
  counts := ![(.branch 19 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))) (.branch 27 (.branch 22 (.branch 21 (.leaf (11)) (.leaf (12))) (.branch 24 (.leaf (13)) (.branch 26 (.leaf (14)) (.leaf (15))))) (.branch 33 (.branch 29 (.leaf (16)) (.branch 31 (.leaf (17)) (.leaf (18)))) (.branch 35 (.leaf (19)) (.branch 37 (.leaf (20)) (.leaf (21))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 9 (.leaf (-10)) (.branch 27 (.leaf (-12)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 34 (.leaf (-15)) (.leaf (-16)))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-17)) (.leaf (-18)))),
  (.branch 12 (.leaf (0)) (.branch 23 (.leaf (-1)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (-9)) (.leaf (-10)))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 32 (.branch 28 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 34 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9))))),
  (.branch 36 (.branch 35 (.leaf (-16)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))),
  (.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.leaf (-3)) (.leaf (-2))),
  (.branch 33 (.branch 31 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-1)) (.leaf (0)))]
def witnessD7_047_737 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (3)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.leaf (4)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_737
  counts := ![(.branch 17 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-20)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-32))),
  (.branch 25 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 27 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-13))))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-32)) (.leaf (-31))) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_047_738 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (1))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (3)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.branch 28 (.leaf (2)) (.leaf (3)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (4)) (.leaf (2)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_738
  counts := ![(.branch 15 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-26)) (.leaf (-35)))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 32 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 35 (.branch 22 (.leaf (-35)) (.leaf (-34))) (.branch 36 (.leaf (-30)) (.branch 37 (.leaf (-26)) (.leaf (-22))))),
  (.branch 20 (.leaf (-6)) (.branch 37 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_047_739 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (2))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_739
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 34 (.branch 31 (.leaf (9)) (.leaf (10))) (.branch 38 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-13)) (.branch 24 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 16 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-20))),
  (.branch 37 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 31 (.branch 25 (.leaf (-20)) (.branch 28 (.leaf (-19)) (.leaf (-18)))) (.branch 34 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-11))))),
  (.branch 35 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 23 (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16))))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_047_740 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (6)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_740
  counts := ![(.branch 18 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))) (.branch 29 (.branch 22 (.branch 20 (.leaf (9)) (.leaf (10))) (.branch 24 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13))))) (.branch 33 (.branch 31 (.leaf (14)) (.leaf (15))) (.branch 35 (.leaf (16)) (.branch 37 (.leaf (17)) (.leaf (18))))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-11)) (.branch 7 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-15)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 27 (.leaf (-13)) (.leaf (-9))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-14))) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_047_741 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 10 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 29 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.branch 28 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (1)) (.leaf (3))) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (6))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_741
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 5 (.leaf (-14)) (.leaf (-17)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-16)) (.leaf (-23)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-10)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.leaf (-26))),
  (.branch 23 (.leaf (0)) (.leaf (-15))),
  (.branch 35 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-8)))),
  (.branch 27 (.leaf (-23)) (.branch 34 (.leaf (-22)) (.leaf (-19)))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 32 (.branch 17 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5))))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-26)) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 16 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21))))) (.branch 21 (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18)))) (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_047_742 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (6)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_742
  counts := ![(.branch 18 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 37 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.branch 24 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-29))),
  (.branch 28 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 30 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 16 (.branch 12 (.branch 10 (.leaf (-29)) (.branch 11 (.leaf (-28)) (.leaf (-27)))) (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23))))) (.branch 19 (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_047_743 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (6))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_743
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 24 (.leaf (10)) (.leaf (11)))) (.branch 31 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.branch 36 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 5 (.leaf (-14)) (.branch 12 (.leaf (-17)) (.leaf (-18))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 26 (.leaf (-12)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-7)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 32 (.leaf (-18)) (.branch 37 (.leaf (-16)) (.leaf (-8)))),
  (.branch 35 (.branch 27 (.leaf (-13)) (.branch 34 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4))))),
  (.leaf (-2)),
  (.branch 36 (.branch 24 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_047_744 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (6))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (6))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_744
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-13)) (.branch 24 (.leaf (-17)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 29 (.leaf (-10)) (.leaf (-17)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 31 (.branch 25 (.leaf (-20)) (.branch 28 (.leaf (-19)) (.leaf (-18)))) (.branch 34 (.leaf (-17)) (.branch 37 (.leaf (-16)) (.leaf (-11))))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.leaf (-17)) (.leaf (-16))),
  (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_047_745 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (6)) (.branch 18 (.leaf (0)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (5)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4)))) (.branch 35 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_745
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))) (.branch 33 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.leaf (13)))))),
  (.branch 20 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-25)) (.leaf (-37)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 29 (.branch 26 (.leaf (-5)) (.leaf (-6))) (.branch 35 (.leaf (-7)) (.leaf (-9))))),
  (.branch 25 (.branch 19 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-37)) (.branch 7 (.leaf (-36)) (.leaf (-35)))) (.branch 13 (.leaf (-34)) (.branch 16 (.leaf (-33)) (.leaf (-32))))) (.branch 28 (.branch 22 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 31 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-26)) (.leaf (-13)))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 29 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_047_746 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (5)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (3)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (6)))) (.branch 35 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_746
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))) (.branch 33 (.branch 30 (.leaf (10)) (.leaf (11))) (.branch 36 (.leaf (12)) (.leaf (13)))))),
  (.branch 20 (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (10)) (.leaf (11)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-25)) (.leaf (-37)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 29 (.branch 26 (.leaf (-5)) (.leaf (-6))) (.branch 35 (.leaf (-7)) (.leaf (-9))))),
  (.branch 25 (.branch 19 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-15)) (.leaf (-16)))),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 32 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 10 (.branch 4 (.leaf (-37)) (.branch 7 (.leaf (-36)) (.leaf (-35)))) (.branch 13 (.leaf (-34)) (.branch 16 (.leaf (-33)) (.leaf (-32))))) (.branch 28 (.branch 22 (.leaf (-31)) (.branch 25 (.leaf (-30)) (.leaf (-29)))) (.branch 34 (.branch 31 (.leaf (-28)) (.leaf (-27))) (.branch 37 (.leaf (-26)) (.leaf (-13)))))),
  (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-3)),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_047_747 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (1)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_747
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 31 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-12)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-8)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-34))),
  (.branch 23 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 34 (.branch 23 (.leaf (-17)) (.leaf (-16))) (.branch 37 (.leaf (-14)) (.leaf (-7)))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.leaf (-5)) (.leaf (-3))),
  (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 21 (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-34)) (.leaf (-33))) (.branch 7 (.leaf (-32)) (.leaf (-31)))) (.branch 10 (.branch 9 (.leaf (-30)) (.leaf (-29))) (.branch 11 (.leaf (-28)) (.leaf (-27))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18))))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 27 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 28 (.leaf (-11)) (.leaf (-10))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_047_748 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_748
  counts := ![(.branch 18 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 23 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 30 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (14)) (.branch 37 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 26 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 28 (.leaf (-12)) (.branch 33 (.leaf (-10)) (.leaf (-8)))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 35 (.branch 34 (.leaf (-10)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.leaf (-31)) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_047_749 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (5))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (4))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_749
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (-7))) (.branch 30 (.leaf (-9)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 24 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5))))),
  (.branch 35 (.branch 33 (.leaf (-8)) (.branch 34 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5))))),
  (.branch 27 (.branch 12 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_047 : Fin 26 → CycleWitness 7 := ![witnessD7_047_724, witnessD7_047_725, witnessD7_047_726, witnessD7_047_727, witnessD7_047_728, witnessD7_047_729, witnessD7_047_730, witnessD7_047_731, witnessD7_047_732, witnessD7_047_733, witnessD7_047_734, witnessD7_047_735, witnessD7_047_736, witnessD7_047_737, witnessD7_047_738, witnessD7_047_739, witnessD7_047_740, witnessD7_047_741, witnessD7_047_742, witnessD7_047_743, witnessD7_047_744, witnessD7_047_745, witnessD7_047_746, witnessD7_047_747, witnessD7_047_748, witnessD7_047_749]
end RealPinwheel.FiveSixths


