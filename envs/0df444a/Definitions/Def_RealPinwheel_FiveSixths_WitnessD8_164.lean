-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_164
-- name    : RealPinwheel_FiveSixths_WitnessD8_164
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T06:22:14.525877+00:00
-- url     : https://prove2.me/theorems/1261c49a-990b-4558-a4f4-cae387dd14ac
-- title:
--   Exact witness block D8_164
-- statement:
--   These exact witnesses represent words 1532 through 1548 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1532–1548; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_164_1531 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (0)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (2)) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (0)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (7)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (4)) (.leaf (0))) (.branch 52 (.leaf (3)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (0)) (.leaf (4))))))))
  code := certificateD8_1531
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 42 (.branch 35 (.branch 30 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 49 (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20)))) (.branch 54 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 56 (.leaf (23)) (.leaf (24))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 41 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-50))),
  (.branch 26 (.leaf (0)) (.leaf (-31))),
  (.branch 45 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 47 (.leaf (-12)) (.branch 52 (.leaf (-10)) (.leaf (-8)))),
  (.branch 54 (.branch 41 (.leaf (-13)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 49 (.branch 42 (.leaf (-9)) (.leaf (-8))) (.branch 56 (.leaf (-7)) (.leaf (-5)))),
  (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 39 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 32 (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-50)) (.branch 9 (.leaf (-49)) (.leaf (-48)))) (.branch 11 (.leaf (-47)) (.branch 12 (.leaf (-46)) (.leaf (-45))))) (.branch 16 (.branch 14 (.leaf (-44)) (.branch 15 (.leaf (-43)) (.leaf (-42)))) (.branch 17 (.leaf (-41)) (.branch 18 (.leaf (-40)) (.leaf (-39)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-38)) (.branch 21 (.leaf (-37)) (.leaf (-36)))) (.branch 23 (.leaf (-35)) (.branch 24 (.leaf (-34)) (.leaf (-33))))) (.branch 28 (.branch 26 (.leaf (-32)) (.branch 27 (.leaf (-31)) (.leaf (-30)))) (.branch 30 (.branch 29 (.leaf (-29)) (.leaf (-28))) (.branch 31 (.leaf (-27)) (.leaf (-26))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 33 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-23)))) (.branch 36 (.leaf (-22)) (.branch 37 (.leaf (-21)) (.leaf (-20))))) (.branch 41 (.branch 39 (.leaf (-19)) (.branch 40 (.leaf (-18)) (.leaf (-17)))) (.branch 42 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.leaf (-31)) (.branch 28 (.leaf (-30)) (.leaf (-29)))) (.branch 31 (.branch 30 (.leaf (-28)) (.leaf (-27))) (.branch 32 (.leaf (-26)) (.leaf (-25))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-23))) (.branch 36 (.leaf (-22)) (.leaf (-21)))) (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.leaf (-17)))))) (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_164_1532 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (1))) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (5)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (3)) (.leaf (0))) (.branch 41 (.leaf (6)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (4))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (1))) (.branch 52 (.leaf (5)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (7))) (.branch 56 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1532
  counts := ![(.branch 26 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))) (.branch 40 (.branch 31 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))) (.branch 49 (.branch 44 (.leaf (10)) (.leaf (11))) (.branch 53 (.leaf (12)) (.leaf (13)))))),
  (.branch 29 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))) (.branch 43 (.branch 33 (.leaf (7)) (.branch 38 (.leaf (8)) (.leaf (9)))) (.branch 51 (.branch 46 (.leaf (10)) (.leaf (11))) (.branch 56 (.leaf (12)) (.leaf (13)))))),
  (.branch 24 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 30 (.leaf (5)) (.branch 36 (.leaf (6)) (.leaf (7)))) (.branch 48 (.leaf (8)) (.branch 54 (.leaf (9)) (.leaf (10)))))),
  (.branch 32 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 39 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 52 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 27 (.leaf (0)) (.branch 55 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-38))) (.branch 8 (.leaf (-54)) (.leaf (-59)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 46 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-26)) (.leaf (-50)))),
  (.branch 45 (.branch 32 (.leaf (0)) (.leaf (-10))) (.branch 50 (.leaf (-13)) (.leaf (-22)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (-28))) (.branch 47 (.leaf (-29)) (.leaf (-31)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (-9))) (.branch 37 (.leaf (-12)) (.leaf (-13)))),
  (.branch 12 (.leaf (0)) (.leaf (-33))),
  (.branch 27 (.leaf (0)) (.branch 55 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 36 (.branch 18 (.branch 9 (.leaf (-59)) (.leaf (-58))) (.branch 27 (.leaf (-57)) (.leaf (-56)))) (.branch 54 (.branch 45 (.leaf (-55)) (.leaf (-54))) (.branch 55 (.leaf (-43)) (.branch 56 (.leaf (-32)) (.leaf (-21)))))),
  (.branch 47 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))),
  (.branch 37 (.branch 25 (.branch 19 (.leaf (-50)) (.leaf (-49))) (.branch 31 (.leaf (-48)) (.leaf (-47)))) (.branch 49 (.branch 43 (.leaf (-46)) (.leaf (-45))) (.branch 55 (.leaf (-44)) (.branch 56 (.leaf (-35)) (.leaf (-26)))))),
  (.branch 53 (.branch 51 (.leaf (-22)) (.branch 52 (.leaf (-17)) (.leaf (-12)))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-2)) (.leaf (0))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-31)) (.leaf (-28))) (.branch 50 (.leaf (-25)) (.branch 51 (.leaf (-22)) (.leaf (-19))))) (.branch 54 (.branch 53 (.leaf (-16)) (.leaf (-13))) (.branch 55 (.leaf (-10)) (.branch 56 (.leaf (-7)) (.leaf (-4)))))),
  (.branch 54 (.branch 38 (.leaf (-13)) (.branch 53 (.leaf (-12)) (.leaf (-10)))) (.branch 55 (.leaf (-8)) (.branch 56 (.leaf (-6)) (.leaf (-4))))),
  (.branch 48 (.branch 44 (.branch 42 (.branch 13 (.leaf (-33)) (.leaf (-32))) (.branch 43 (.leaf (-30)) (.leaf (-28)))) (.branch 46 (.branch 45 (.leaf (-26)) (.leaf (-24))) (.branch 47 (.leaf (-22)) (.leaf (-20))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-18)) (.leaf (-16))) (.branch 51 (.leaf (-14)) (.leaf (-12)))) (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))))),
  (.branch 56 (.leaf (-4)) (.leaf (-2)))]
def witnessD8_164_1533 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (5))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (4)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (6)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (3)) (.leaf (7))))))))
  code := certificateD8_1533
  counts := ![(.branch 27 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 48 (.branch 46 (.leaf (14)) (.leaf (15))) (.branch 51 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 26 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 37 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 56 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 57 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-12)))) (.branch 32 (.branch 29 (.leaf (-13)) (.leaf (-14))) (.branch 48 (.leaf (-15)) (.branch 51 (.leaf (-16)) (.leaf (-17)))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-38))),
  (.branch 38 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 52 (.leaf (-17)) (.branch 56 (.leaf (-14)) (.leaf (-10)))),
  (.branch 55 (.branch 50 (.leaf (-13)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.branch 55 (.branch 54 (.leaf (-12)) (.leaf (-9))) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 38 (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-38)) (.leaf (-37))) (.branch 22 (.leaf (-36)) (.leaf (-35)))) (.branch 25 (.branch 24 (.leaf (-34)) (.leaf (-33))) (.branch 26 (.leaf (-32)) (.branch 27 (.leaf (-31)) (.leaf (-30)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-29)) (.leaf (-28))) (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25))))) (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-23))) (.branch 36 (.leaf (-22)) (.branch 37 (.leaf (-21)) (.leaf (-20))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD8_164_1534 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (1)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (2))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (2)) (.leaf (7))) (.branch 56 (.leaf (1)) (.leaf (3))))))))
  code := certificateD8_1534
  counts := ![(.branch 27 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 29 (.branch 14 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))) (.branch 45 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 28 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 55 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 40 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.leaf (-40))),
  (.branch 36 (.leaf (0)) (.leaf (-21))),
  (.branch 55 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (-4)),
  (.branch 55 (.branch 48 (.leaf (-11)) (.leaf (-9))) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.branch 51 (.leaf (-2)) (.leaf (0))),
  (.branch 54 (.branch 52 (.leaf (-12)) (.branch 53 (.leaf (-10)) (.leaf (-8)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 37 (.branch 27 (.branch 22 (.branch 19 (.branch 18 (.leaf (-40)) (.leaf (-39))) (.branch 20 (.leaf (-38)) (.branch 21 (.leaf (-37)) (.leaf (-36))))) (.branch 24 (.branch 23 (.leaf (-35)) (.leaf (-34))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 30 (.leaf (-28)) (.branch 31 (.leaf (-27)) (.leaf (-26))))) (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-24))) (.branch 35 (.leaf (-23)) (.branch 36 (.leaf (-22)) (.leaf (-21))))))) (.branch 47 (.branch 42 (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16))))) (.branch 44 (.branch 43 (.leaf (-15)) (.leaf (-14))) (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))))) (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 46 (.branch 41 (.branch 38 (.branch 37 (.leaf (-21)) (.leaf (-20))) (.branch 39 (.leaf (-19)) (.branch 40 (.leaf (-18)) (.leaf (-17))))) (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))))) (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 56 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_164_1535 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (3)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (4)) (.branch 37 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (7))) (.branch 48 (.leaf (0)) (.leaf (4))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (3))) (.branch 52 (.leaf (2)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (4))) (.branch 56 (.leaf (2)) (.leaf (3))))))))
  code := certificateD8_1535
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 47 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 41 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-48))),
  (.branch 28 (.leaf (0)) (.leaf (-29))),
  (.branch 47 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 54 (.branch 44 (.leaf (-18)) (.branch 49 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-4)),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 43 (.leaf (-7)) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.branch 33 (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-48)) (.branch 11 (.leaf (-47)) (.leaf (-46)))) (.branch 13 (.leaf (-45)) (.branch 14 (.leaf (-44)) (.leaf (-43))))) (.branch 18 (.branch 16 (.leaf (-42)) (.branch 17 (.leaf (-41)) (.leaf (-40)))) (.branch 19 (.leaf (-39)) (.branch 20 (.leaf (-38)) (.leaf (-37)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-36)) (.branch 23 (.leaf (-35)) (.leaf (-34)))) (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31))))) (.branch 30 (.branch 28 (.leaf (-30)) (.branch 29 (.leaf (-29)) (.leaf (-28)))) (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25))))))) (.branch 45 (.branch 39 (.branch 36 (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-23)) (.leaf (-22)))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19))))) (.branch 42 (.branch 40 (.leaf (-18)) (.branch 41 (.leaf (-17)) (.leaf (-16)))) (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))))) (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-29)) (.branch 30 (.leaf (-28)) (.leaf (-27)))) (.branch 33 (.branch 32 (.leaf (-26)) (.leaf (-25))) (.branch 34 (.leaf (-24)) (.leaf (-23))))) (.branch 38 (.branch 36 (.leaf (-22)) (.branch 37 (.leaf (-21)) (.leaf (-20)))) (.branch 40 (.branch 39 (.leaf (-19)) (.leaf (-18))) (.branch 41 (.leaf (-17)) (.leaf (-16)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-15)) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 52 (.branch 49 (.branch 48 (.leaf (-10)) (.leaf (-9))) (.branch 50 (.leaf (-8)) (.branch 51 (.leaf (-7)) (.leaf (-6))))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_164_1536 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (4)) (.branch 23 (.leaf (5)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (6))) (.branch 27 (.leaf (3)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (4)) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (7)) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (5)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (0)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (4))) (.branch 52 (.leaf (1)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (7))) (.branch 56 (.leaf (3)) (.leaf (4))))))))
  code := certificateD8_1536
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 33 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 52 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 56 (.leaf (7)) (.leaf (8)))))),
  (.branch 29 (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 37 (.leaf (4)) (.leaf (5))) (.branch 51 (.leaf (6)) (.branch 57 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 33 (.leaf (-11)) (.branch 52 (.leaf (-12)) (.leaf (-13))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 24 (.leaf (-22)) (.branch 38 (.leaf (-24)) (.leaf (-26))))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-13)))),
  (.branch 43 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 31 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 50 (.branch 40 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 54 (.branch 53 (.leaf (-13)) (.leaf (-11))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-7)) (.leaf (-5))))),
  (.branch 54 (.branch 39 (.leaf (-26)) (.leaf (-23))) (.branch 55 (.leaf (-18)) (.branch 56 (.leaf (-13)) (.leaf (-8))))),
  (.branch 20 (.leaf (-13)) (.branch 49 (.leaf (-12)) (.leaf (-8)))),
  (.branch 44 (.leaf (-1)) (.leaf (0))),
  (.branch 53 (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.branch 51 (.branch 48 (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 56 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_164_1537 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (0))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (4)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (7)) (.leaf (4)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (3)) (.leaf (2))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 52 (.leaf (4)) (.leaf (3)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (2))) (.branch 56 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_1537
  counts := ![(.branch 28 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 43 (.branch 35 (.branch 32 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 51 (.branch 47 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.leaf (15)))))),
  (.branch 27 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 30 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 29 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 48 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 33 (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 52 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-15)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 40 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-9)) (.branch 53 (.leaf (-10)) (.leaf (-11))))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-51))),
  (.branch 25 (.leaf (0)) (.leaf (-32))),
  (.branch 44 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-10)) (.leaf (-5)))),
  (.branch 51 (.leaf (-5)) (.leaf (-4))),
  (.branch 43 (.leaf (-7)) (.branch 56 (.leaf (-6)) (.leaf (-3)))),
  (.branch 55 (.branch 54 (.leaf (-11)) (.leaf (-9))) (.branch 56 (.leaf (-7)) (.leaf (-5)))),
  (.branch 39 (.leaf (-2)) (.branch 46 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 18 (.branch 12 (.branch 9 (.branch 7 (.leaf (-51)) (.branch 8 (.leaf (-50)) (.leaf (-49)))) (.branch 10 (.leaf (-48)) (.branch 11 (.leaf (-47)) (.leaf (-46))))) (.branch 15 (.branch 13 (.leaf (-45)) (.branch 14 (.leaf (-44)) (.leaf (-43)))) (.branch 16 (.leaf (-42)) (.branch 17 (.leaf (-41)) (.leaf (-40)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-39)) (.branch 20 (.leaf (-38)) (.leaf (-37)))) (.branch 22 (.leaf (-36)) (.branch 23 (.leaf (-35)) (.leaf (-34))))) (.branch 27 (.branch 25 (.leaf (-33)) (.branch 26 (.leaf (-32)) (.leaf (-31)))) (.branch 29 (.branch 28 (.leaf (-30)) (.leaf (-29))) (.branch 30 (.leaf (-28)) (.leaf (-27))))))) (.branch 44 (.branch 37 (.branch 34 (.branch 32 (.leaf (-26)) (.branch 33 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.leaf (-23)) (.branch 36 (.leaf (-22)) (.leaf (-21))))) (.branch 40 (.branch 38 (.leaf (-20)) (.branch 39 (.leaf (-19)) (.leaf (-18)))) (.branch 42 (.branch 41 (.leaf (-17)) (.leaf (-16))) (.branch 43 (.leaf (-15)) (.leaf (-14)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 41 (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-32)) (.leaf (-31))) (.branch 28 (.leaf (-30)) (.leaf (-29)))) (.branch 31 (.branch 30 (.leaf (-28)) (.leaf (-27))) (.branch 32 (.leaf (-26)) (.leaf (-25))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-23))) (.branch 36 (.leaf (-22)) (.leaf (-21)))) (.branch 39 (.branch 38 (.leaf (-20)) (.leaf (-19))) (.branch 40 (.leaf (-18)) (.leaf (-17)))))) (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-13)) (.branch 46 (.leaf (-12)) (.leaf (-11)))) (.branch 48 (.leaf (-10)) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_164_1538 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (7)) (.branch 9 (.leaf (1)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (7)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (2)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (3)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (5)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (7)) (.leaf (1))) (.branch 48 (.leaf (4)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (3)) (.leaf (0))) (.branch 52 (.leaf (5)) (.leaf (2)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (0))) (.branch 56 (.leaf (6)) (.leaf (3))))))))
  code := certificateD8_1538
  counts := ![(.branch 26 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))) (.branch 42 (.branch 32 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 49 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 51 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 28 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 35 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 54 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 50 (.branch 38 (.leaf (3)) (.leaf (4))) (.branch 57 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 32 (.branch 13 (.leaf (-13)) (.leaf (-15))) (.branch 51 (.leaf (-16)) (.leaf (-17))))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 40 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (-3)) (.leaf (-6)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-42))) (.branch 25 (.leaf (-44)) (.leaf (-46)))),
  (.branch 6 (.leaf (0)) (.leaf (-27))),
  (.branch 10 (.leaf (0)) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 52 (.leaf (-17)) (.branch 56 (.leaf (-13)) (.leaf (-8)))),
  (.branch 48 (.branch 41 (.leaf (-11)) (.leaf (-10))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-7)) (.leaf (-5))))),
  (.branch 54 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 52 (.branch 39 (.leaf (-6)) (.branch 51 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.branch 53 (.leaf (-3)) (.leaf (-2))) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 52 (.branch 49 (.branch 26 (.leaf (-46)) (.leaf (-45))) (.branch 50 (.leaf (-40)) (.branch 51 (.leaf (-35)) (.leaf (-30))))) (.branch 54 (.branch 53 (.leaf (-25)) (.leaf (-20))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 53 (.branch 7 (.leaf (-27)) (.branch 30 (.leaf (-26)) (.leaf (-25)))) (.branch 55 (.branch 54 (.leaf (-20)) (.leaf (-15))) (.branch 56 (.leaf (-10)) (.leaf (-5))))),
  (.branch 45 (.leaf (-8)) (.leaf (-5))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_164_1539 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (2)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (5)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (4)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (3))) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (7)) (.branch 37 (.leaf (5)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (6)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (5)) (.leaf (2))) (.branch 52 (.leaf (3)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (1)) (.leaf (7))) (.branch 56 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_1539
  counts := ![(.branch 27 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 29 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 32 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 43 (.branch 33 (.leaf (3)) (.leaf (4))) (.branch 52 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 36 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 49 (.leaf (-6)) (.leaf (-7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))) (.branch 29 (.leaf (-5)) (.branch 48 (.leaf (-6)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 31 (.leaf (-12)) (.leaf (-14)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (-6))) (.branch 50 (.leaf (-8)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 41 (.leaf (-3)) (.leaf (-4)))),
  (.branch 17 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.branch 55 (.branch 49 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 54 (.branch 53 (.leaf (-10)) (.leaf (-8))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-4)) (.leaf (-2))))),
  (.branch 51 (.branch 48 (.branch 32 (.leaf (-14)) (.leaf (-13))) (.branch 49 (.leaf (-12)) (.branch 50 (.leaf (-11)) (.leaf (-10))))) (.branch 54 (.branch 52 (.leaf (-9)) (.branch 53 (.leaf (-8)) (.leaf (-7)))) (.branch 55 (.leaf (-6)) (.branch 56 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 53 (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 55 (.branch 54 (.leaf (-7)) (.leaf (-6))) (.branch 56 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 56 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_164_1540 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (7)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (3)) (.leaf (2)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (5)) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (7)) (.leaf (6))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (5)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (6)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (3))) (.branch 48 (.leaf (4)) (.leaf (0))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (2)) (.leaf (7))) (.branch 52 (.leaf (5)) (.leaf (1)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (6)) (.leaf (2))))))))
  code := certificateD8_1540
  counts := ![(.branch 25 (.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))) (.branch 40 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 46 (.leaf (7)) (.branch 53 (.leaf (8)) (.leaf (9)))))),
  (.branch 31 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 50 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))) (.branch 42 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 47 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 26 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 37 (.leaf (3)) (.branch 48 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))) (.branch 41 (.leaf (3)) (.branch 52 (.leaf (4)) (.leaf (5))))),
  (.branch 33 (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))) (.branch 45 (.leaf (3)) (.branch 56 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 51 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 43 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 28 (.leaf (-5)) (.branch 47 (.leaf (-7)) (.leaf (-9))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-42))) (.branch 48 (.leaf (-44)) (.leaf (-45)))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (-22))) (.branch 29 (.leaf (-24)) (.leaf (-26)))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 50 (.branch 40 (.leaf (-15)) (.branch 45 (.leaf (-14)) (.leaf (-13)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 54 (.branch 47 (.leaf (-14)) (.leaf (-12))) (.branch 55 (.leaf (-9)) (.branch 56 (.leaf (-6)) (.leaf (-3))))),
  (.branch 51 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 52 (.leaf (-2)) (.leaf (0)))),
  (.branch 48 (.leaf (-9)) (.branch 56 (.leaf (-8)) (.leaf (-7)))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-45)) (.leaf (-40))) (.branch 51 (.leaf (-35)) (.leaf (-30)))) (.branch 54 (.branch 53 (.leaf (-25)) (.leaf (-20))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-10)) (.leaf (-5)))))),
  (.branch 54 (.branch 30 (.leaf (-26)) (.branch 53 (.leaf (-25)) (.leaf (-20)))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-10)) (.leaf (-5))))),
  (.branch 11 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.branch 54 (.branch 52 (.leaf (-6)) (.branch 53 (.leaf (-5)) (.leaf (-4)))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_164_1541 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (6)) (.branch 23 (.leaf (0)) (.leaf (3)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (3)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (7)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (4))) (.branch 48 (.leaf (1)) (.leaf (3))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (0)) (.leaf (2))) (.branch 52 (.leaf (1)) (.leaf (4)))) (.branch 55 (.branch 54 (.leaf (0)) (.leaf (3))) (.branch 56 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_1541
  counts := ![(.branch 27 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 35 (.branch 31 (.leaf (8)) (.leaf (9))) (.branch 39 (.leaf (10)) (.leaf (11)))) (.branch 50 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 54 (.leaf (14)) (.leaf (15)))))),
  (.branch 29 (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))) (.branch 44 (.branch 37 (.branch 33 (.leaf (8)) (.leaf (9))) (.branch 40 (.leaf (10)) (.leaf (11)))) (.branch 52 (.branch 48 (.leaf (12)) (.leaf (13))) (.branch 56 (.leaf (14)) (.leaf (15)))))),
  (.branch 32 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))) (.branch 45 (.branch 38 (.leaf (5)) (.leaf (6))) (.branch 51 (.leaf (7)) (.branch 57 (.leaf (8)) (.leaf (9)))))),
  (.branch 30 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))) (.branch 43 (.branch 36 (.leaf (5)) (.leaf (6))) (.branch 49 (.leaf (7)) (.branch 55 (.leaf (8)) (.leaf (9)))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 47 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 53 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 15 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-9)) (.branch 53 (.leaf (-14)) (.leaf (-19))))),
  (.branch 3 (.leaf (0)) (.leaf (-54))),
  (.branch 22 (.leaf (0)) (.leaf (-35))),
  (.branch 41 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 51 (.branch 43 (.leaf (-18)) (.branch 47 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.leaf (-15)) (.branch 56 (.leaf (-10)) (.leaf (-5))))),
  (.branch 45 (.branch 41 (.leaf (-9)) (.leaf (-8))) (.branch 49 (.leaf (-7)) (.branch 53 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 56 (.leaf (-6)) (.leaf (-3))),
  (.branch 55 (.branch 54 (.leaf (-19)) (.leaf (-18))) (.branch 56 (.leaf (-17)) (.leaf (-16)))),
  (.branch 30 (.branch 16 (.branch 9 (.branch 6 (.branch 4 (.leaf (-54)) (.branch 5 (.leaf (-53)) (.leaf (-52)))) (.branch 7 (.leaf (-51)) (.branch 8 (.leaf (-50)) (.leaf (-49))))) (.branch 12 (.branch 10 (.leaf (-48)) (.branch 11 (.leaf (-47)) (.leaf (-46)))) (.branch 14 (.branch 13 (.leaf (-45)) (.leaf (-44))) (.branch 15 (.leaf (-43)) (.leaf (-42)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (-41)) (.branch 18 (.leaf (-40)) (.leaf (-39)))) (.branch 21 (.branch 20 (.leaf (-38)) (.leaf (-37))) (.branch 22 (.leaf (-36)) (.leaf (-35))))) (.branch 26 (.branch 24 (.leaf (-34)) (.branch 25 (.leaf (-33)) (.leaf (-32)))) (.branch 28 (.branch 27 (.leaf (-31)) (.leaf (-30))) (.branch 29 (.leaf (-29)) (.leaf (-28))))))) (.branch 43 (.branch 36 (.branch 33 (.branch 31 (.leaf (-27)) (.branch 32 (.leaf (-26)) (.leaf (-25)))) (.branch 34 (.leaf (-24)) (.branch 35 (.leaf (-23)) (.leaf (-22))))) (.branch 39 (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19)))) (.branch 41 (.branch 40 (.leaf (-18)) (.leaf (-17))) (.branch 42 (.leaf (-16)) (.leaf (-15)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (-14)) (.branch 45 (.leaf (-13)) (.leaf (-12)))) (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.leaf (-8))))) (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 39 (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-35)) (.leaf (-34))) (.branch 25 (.leaf (-33)) (.leaf (-32)))) (.branch 28 (.branch 27 (.leaf (-31)) (.leaf (-30))) (.branch 29 (.leaf (-29)) (.leaf (-28))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-27)) (.leaf (-26))) (.branch 33 (.leaf (-25)) (.leaf (-24)))) (.branch 36 (.branch 35 (.leaf (-23)) (.leaf (-22))) (.branch 37 (.leaf (-21)) (.branch 38 (.leaf (-20)) (.leaf (-19))))))) (.branch 48 (.branch 43 (.branch 41 (.branch 40 (.leaf (-18)) (.leaf (-17))) (.branch 42 (.leaf (-16)) (.leaf (-15)))) (.branch 45 (.branch 44 (.leaf (-14)) (.leaf (-13))) (.branch 46 (.leaf (-12)) (.branch 47 (.leaf (-11)) (.leaf (-10)))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.branch 56 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 49 (.branch 45 (.branch 43 (.branch 42 (.leaf (-16)) (.leaf (-15))) (.branch 44 (.leaf (-14)) (.leaf (-13)))) (.branch 47 (.branch 46 (.leaf (-12)) (.leaf (-11))) (.branch 48 (.leaf (-10)) (.leaf (-9))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_164_1542 : CycleWitness 8 where
  length := 57
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (7))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (3))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (7)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (5))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (6))) (.branch 41 (.leaf (2)) (.leaf (1)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (3)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (5))))) (.branch 53 (.branch 51 (.branch 50 (.leaf (7)) (.leaf (2))) (.branch 52 (.leaf (1)) (.leaf (0)))) (.branch 55 (.branch 54 (.leaf (6)) (.leaf (3))) (.branch 56 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_1542
  counts := ![(.branch 24 (.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 43 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))) (.branch 52 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 57 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 26 (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 55 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 31 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-49))) (.branch 30 (.leaf (-50)) (.branch 44 (.leaf (-51)) (.leaf (-52))))),
  (.branch 6 (.leaf (0)) (.leaf (-33))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-13)) (.leaf (-14)))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 54 (.branch 44 (.leaf (-18)) (.branch 49 (.leaf (-17)) (.leaf (-16)))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4))))),
  (.branch 48 (.branch 43 (.leaf (-3)) (.leaf (-2))) (.branch 53 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 52 (.leaf (-5)) (.leaf (-4)))),
  (.branch 46 (.leaf (-5)) (.branch 56 (.leaf (-4)) (.leaf (-2)))),
  (.branch 50 (.branch 47 (.branch 45 (.leaf (-52)) (.branch 46 (.leaf (-48)) (.leaf (-44)))) (.branch 48 (.leaf (-40)) (.branch 49 (.leaf (-36)) (.leaf (-32))))) (.branch 53 (.branch 51 (.leaf (-28)) (.branch 52 (.leaf (-24)) (.leaf (-20)))) (.branch 55 (.branch 54 (.leaf (-16)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 52 (.branch 50 (.branch 7 (.leaf (-33)) (.leaf (-32))) (.branch 51 (.leaf (-28)) (.leaf (-24)))) (.branch 54 (.branch 53 (.leaf (-20)) (.leaf (-16))) (.branch 55 (.leaf (-12)) (.branch 56 (.leaf (-8)) (.leaf (-4)))))),
  (.branch 55 (.branch 26 (.leaf (-14)) (.leaf (-12))) (.branch 56 (.leaf (-8)) (.leaf (-4)))),
  (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 55 (.branch 54 (.leaf (-4)) (.leaf (-3))) (.branch 56 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_164_1543 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (7))) (.branch 27 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (2)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (2)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (6))) (.branch 55 (.leaf (0)) (.leaf (3)))))))
  code := certificateD8_1543
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.branch 26 (.leaf (18)) (.leaf (19))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (20)) (.leaf (21))) (.branch 31 (.leaf (22)) (.branch 33 (.leaf (23)) (.leaf (24))))) (.branch 37 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 38 (.leaf (27)) (.branch 40 (.leaf (28)) (.leaf (29)))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (30)) (.leaf (31))) (.branch 45 (.leaf (32)) (.branch 47 (.leaf (33)) (.leaf (34))))) (.branch 52 (.branch 50 (.leaf (35)) (.branch 51 (.leaf (36)) (.leaf (37)))) (.branch 54 (.leaf (38)) (.branch 55 (.leaf (39)) (.leaf (40)))))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-45))),
  (.branch 39 (.leaf (0)) (.leaf (-17))),
  (.branch 53 (.leaf (0)) (.leaf (-3))),
  (.branch 25 (.leaf (0)) (.leaf (-31)))]
  high := ![(.branch 53 (.leaf (-6)) (.leaf (-5))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-45)) (.leaf (-44))) (.branch 14 (.leaf (-43)) (.branch 15 (.leaf (-42)) (.leaf (-41))))) (.branch 19 (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38)))) (.branch 20 (.leaf (-37)) (.branch 21 (.leaf (-36)) (.leaf (-35)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-34)) (.leaf (-33))) (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30))))) (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.leaf (-26)) (.branch 32 (.leaf (-25)) (.leaf (-24))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_164_1544 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 35 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.leaf (3)))) (.branch 39 (.branch 38 (.leaf (0)) (.leaf (5))) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 49 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (0)) (.leaf (7)))) (.branch 53 (.branch 52 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (2)))))))
  code := certificateD8_1544
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (6))) (.branch 10 (.leaf (7)) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (10)) (.leaf (11))) (.branch 17 (.leaf (12)) (.branch 19 (.leaf (13)) (.leaf (14))))) (.branch 23 (.branch 22 (.leaf (15)) (.leaf (16))) (.branch 24 (.leaf (17)) (.branch 26 (.leaf (18)) (.leaf (19))))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (20)) (.leaf (21))) (.branch 31 (.leaf (22)) (.branch 33 (.leaf (23)) (.leaf (24))))) (.branch 37 (.branch 36 (.leaf (25)) (.leaf (26))) (.branch 38 (.leaf (27)) (.branch 40 (.leaf (28)) (.leaf (29)))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (30)) (.leaf (31))) (.branch 45 (.leaf (32)) (.branch 47 (.leaf (33)) (.leaf (34))))) (.branch 52 (.branch 50 (.leaf (35)) (.branch 51 (.leaf (36)) (.leaf (37)))) (.branch 54 (.leaf (38)) (.branch 55 (.leaf (39)) (.leaf (40)))))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.branch 25 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 21 (.leaf (0)) (.leaf (-35))),
  (.branch 49 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 53 (.leaf (-6)) (.leaf (-5))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-10)) (.leaf (-9))) (.branch 49 (.leaf (-8)) (.branch 50 (.leaf (-7)) (.leaf (-6))))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-35)) (.leaf (-34))) (.branch 24 (.leaf (-33)) (.leaf (-32)))) (.branch 27 (.branch 26 (.leaf (-31)) (.leaf (-30))) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_164_1545 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 8 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (5))))))) (.branch 42 (.branch 36 (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 37 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (6)))))) (.branch 50 (.branch 46 (.branch 45 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 52 (.branch 51 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (7))))))))
  code := certificateD8_1545
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.leaf (12)))) (.branch 22 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 31 (.leaf (20)) (.leaf (21)))) (.branch 36 (.branch 35 (.leaf (22)) (.leaf (23))) (.branch 38 (.leaf (24)) (.branch 40 (.leaf (25)) (.leaf (26)))))) (.branch 49 (.branch 44 (.branch 43 (.leaf (27)) (.leaf (28))) (.branch 45 (.leaf (29)) (.branch 47 (.leaf (30)) (.leaf (31))))) (.branch 52 (.branch 50 (.leaf (32)) (.leaf (33))) (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))))))),
  (.branch 25 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 39 (.branch 32 (.leaf (4)) (.leaf (5))) (.branch 46 (.leaf (6)) (.branch 53 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 31 (.branch 17 (.leaf (-9)) (.leaf (-11))) (.branch 45 (.leaf (-13)) (.leaf (-15))))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-42))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.branch 42 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 46 (.leaf (-15)) (.branch 51 (.leaf (-14)) (.leaf (-13)))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-42)) (.leaf (-41))) (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38))))) (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 32 (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22))))))) (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD8_164_1546 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.leaf (0))) (.branch 39 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (1)) (.leaf (0))) (.branch 53 (.leaf (7)) (.branch 55 (.leaf (0)) (.leaf (2))))))))
  code := certificateD8_1546
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.leaf (12)))) (.branch 23 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 32 (.leaf (20)) (.leaf (21)))) (.branch 37 (.branch 35 (.leaf (22)) (.leaf (23))) (.branch 38 (.leaf (24)) (.branch 40 (.leaf (25)) (.leaf (26)))))) (.branch 49 (.branch 44 (.branch 43 (.leaf (27)) (.leaf (28))) (.branch 46 (.leaf (29)) (.branch 47 (.leaf (30)) (.leaf (31))))) (.branch 52 (.branch 51 (.leaf (32)) (.leaf (33))) (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 31 (.leaf (4)) (.leaf (5))) (.branch 45 (.leaf (6)) (.branch 50 (.leaf (7)) (.leaf (8)))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-8)))) (.branch 36 (.leaf (-10)) (.branch 50 (.leaf (-12)) (.leaf (-14))))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-45))),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 39 (.leaf (0)) (.leaf (-17))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 48 (.leaf (-11)) (.leaf (-9))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-13)) (.leaf (-12)))) (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-45)) (.leaf (-44))) (.branch 14 (.leaf (-43)) (.branch 15 (.leaf (-42)) (.leaf (-41))))) (.branch 19 (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38)))) (.branch 20 (.leaf (-37)) (.branch 21 (.leaf (-36)) (.leaf (-35)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-34)) (.leaf (-33))) (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30))))) (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.leaf (-26)) (.branch 32 (.leaf (-25)) (.leaf (-24))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_164_1547 : CycleWitness 8 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (6)) (.branch 27 (.leaf (0)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.branch 34 (.leaf (4)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.leaf (0))) (.branch 39 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 44 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (0)) (.branch 48 (.leaf (4)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.leaf (0))) (.branch 53 (.leaf (7)) (.branch 55 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_1547
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (9)) (.leaf (10))) (.branch 18 (.leaf (11)) (.leaf (12)))) (.branch 23 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 24 (.leaf (15)) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 41 (.branch 33 (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 32 (.leaf (20)) (.leaf (21)))) (.branch 37 (.branch 35 (.leaf (22)) (.leaf (23))) (.branch 38 (.leaf (24)) (.branch 40 (.leaf (25)) (.leaf (26)))))) (.branch 49 (.branch 44 (.branch 43 (.leaf (27)) (.leaf (28))) (.branch 46 (.leaf (29)) (.branch 47 (.leaf (30)) (.leaf (31))))) (.branch 52 (.branch 51 (.leaf (32)) (.leaf (33))) (.branch 54 (.leaf (34)) (.branch 55 (.leaf (35)) (.leaf (36)))))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 50 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 48 (.leaf (-11)) (.leaf (-9))),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_164 : Fin 17 → CycleWitness 8 := ![witnessD8_164_1531, witnessD8_164_1532, witnessD8_164_1533, witnessD8_164_1534, witnessD8_164_1535, witnessD8_164_1536, witnessD8_164_1537, witnessD8_164_1538, witnessD8_164_1539, witnessD8_164_1540, witnessD8_164_1541, witnessD8_164_1542, witnessD8_164_1543, witnessD8_164_1544, witnessD8_164_1545, witnessD8_164_1546, witnessD8_164_1547]
end RealPinwheel.FiveSixths


