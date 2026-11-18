-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_035
-- name    : RealPinwheel_FiveSixths_WitnessD7_035
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:06.953181+00:00
-- url     : https://prove2.me/theorems/fa67da6e-01b8-43e8-955d-a472a99c6d86
-- title:
--   Exact witness block D7_035
-- statement:
--   These exact witnesses represent words 454 through 473 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 454–473; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_035_453 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (6))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_453
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.branch 48 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-30))),
  (.branch 42 (.leaf (0)) (.leaf (-6)))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))) (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_035_454 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (5)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_454
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 28 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-39))),
  (.branch 33 (.leaf (0)) (.leaf (-15))),
  (.branch 45 (.leaf (0)) (.leaf (-3))),
  (.branch 21 (.leaf (0)) (.leaf (-27)))]
  high := ![(.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 28 (.branch 18 (.branch 13 (.branch 11 (.branch 10 (.leaf (-39)) (.leaf (-38))) (.branch 12 (.leaf (-37)) (.leaf (-36)))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.branch 27 (.branch 24 (.branch 22 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_035_455 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (5)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (4)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (6)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_455
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 28 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 44 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 24 (.branch 22 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_035_456 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_456
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 36 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))) (.branch 32 (.leaf (-8)) (.branch 44 (.leaf (-10)) (.leaf (-12))))),
  (.branch 12 (.leaf (0)) (.leaf (-36))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.branch 36 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9)))),
  (.branch 30 (.branch 21 (.branch 16 (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.leaf (-33)))) (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24)))) (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))))) (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_035_457 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_457
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-32))),
  (.branch 32 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-32)) (.leaf (-31))) (.branch 19 (.leaf (-30)) (.leaf (-29)))) (.branch 22 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 23 (.leaf (-26)) (.leaf (-25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 27 (.leaf (-22)) (.leaf (-21)))) (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-17)))))) (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_035_458 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (3)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_458
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 28 (.leaf (-5)) (.branch 40 (.leaf (-7)) (.leaf (-9))))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-29))),
  (.branch 43 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-9)) (.leaf (-8))) (.branch 43 (.leaf (-7)) (.leaf (-6)))) (.branch 46 (.branch 45 (.leaf (-5)) (.leaf (-4))) (.branch 47 (.leaf (-3)) (.leaf (-2))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 35 (.branch 33 (.branch 32 (.leaf (-17)) (.leaf (-16))) (.branch 34 (.leaf (-15)) (.leaf (-14)))) (.branch 37 (.branch 36 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.leaf (-10))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 26 (.branch 22 (.branch 20 (.leaf (-29)) (.branch 21 (.leaf (-28)) (.leaf (-27)))) (.branch 24 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.leaf (-23))))) (.branch 29 (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_035_459 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_459
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_035_460 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (6)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_460
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 42 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 46 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 43 (.branch 41 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.leaf (-1)) (.leaf (0)))]
def witnessD7_035_461 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (6))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (5)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 46 (.leaf (6)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_461
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 44 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.leaf (-1)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_035_462 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (5)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (3)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_462
  counts := ![(.branch 22 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 35 (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.branch 33 (.leaf (12)) (.leaf (13))))) (.branch 41 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 43 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 24 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 37 (.branch 31 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 34 (.leaf (10)) (.leaf (11)))) (.branch 44 (.branch 40 (.leaf (12)) (.leaf (13))) (.branch 47 (.leaf (14)) (.leaf (15)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 45 (.leaf (5)) (.leaf (6))))),
  (.branch 26 (.branch 10 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 48 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-41))),
  (.branch 23 (.leaf (0)) (.leaf (-25))),
  (.branch 39 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 44 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 41 (.leaf (-8)) (.leaf (-5))),
  (.branch 46 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 43 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 44 (.leaf (-2)) (.branch 45 (.leaf (-1)) (.leaf (0))))),
  (.branch 27 (.branch 17 (.branch 12 (.branch 9 (.branch 8 (.leaf (-41)) (.leaf (-40))) (.branch 10 (.leaf (-39)) (.branch 11 (.leaf (-38)) (.leaf (-37))))) (.branch 14 (.branch 13 (.leaf (-36)) (.leaf (-35))) (.branch 15 (.leaf (-34)) (.branch 16 (.leaf (-33)) (.leaf (-32)))))) (.branch 22 (.branch 19 (.branch 18 (.leaf (-31)) (.leaf (-30))) (.branch 20 (.leaf (-29)) (.branch 21 (.leaf (-28)) (.leaf (-27))))) (.branch 24 (.branch 23 (.leaf (-26)) (.leaf (-25))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))))) (.branch 37 (.branch 32 (.branch 29 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 30 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17))))) (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 35 (.branch 29 (.branch 26 (.branch 24 (.leaf (-25)) (.branch 25 (.leaf (-24)) (.leaf (-23)))) (.branch 27 (.leaf (-22)) (.branch 28 (.leaf (-21)) (.leaf (-20))))) (.branch 32 (.branch 30 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-17)))) (.branch 33 (.leaf (-16)) (.branch 34 (.leaf (-15)) (.leaf (-14)))))) (.branch 41 (.branch 38 (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_035_463 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (4)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_463
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 24 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 28 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-40))),
  (.branch 32 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 43 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 47 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 44 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-40)) (.leaf (-39))) (.branch 11 (.leaf (-38)) (.branch 12 (.leaf (-37)) (.leaf (-36))))) (.branch 15 (.branch 14 (.leaf (-35)) (.leaf (-34))) (.branch 16 (.leaf (-33)) (.branch 17 (.leaf (-32)) (.leaf (-31)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-30)) (.leaf (-29))) (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26))))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.branch 27 (.leaf (-22)) (.leaf (-21))))))) (.branch 38 (.branch 33 (.branch 30 (.branch 29 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))))) (.branch 43 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_035_464 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (4)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_464
  counts := ![(.branch 22 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 38 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 47 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 35 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-10)))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (-4))) (.branch 43 (.leaf (-7)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 43 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.leaf (-10)) (.branch 39 (.leaf (-9)) (.leaf (-8)))),
  (.branch 45 (.branch 44 (.leaf (-9)) (.leaf (-8))) (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5))))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_035_465 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (4)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (6)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (4)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (5)) (.branch 41 (.leaf (3)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (4)) (.leaf (6))))))))
  code := certificateD7_465
  counts := ![(.branch 21 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 45 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_035_466 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (6)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (4))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (6)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_466
  counts := ![(.branch 22 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 35 (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.branch 33 (.leaf (12)) (.leaf (13))))) (.branch 41 (.branch 38 (.leaf (14)) (.leaf (15))) (.branch 43 (.leaf (16)) (.branch 46 (.leaf (17)) (.leaf (18))))))),
  (.branch 20 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 44 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-3)))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_035_467 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (4)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (4)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_467
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-8)))) (.branch 30 (.leaf (-10)) (.branch 42 (.leaf (-12)) (.leaf (-14))))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.leaf (-1)),
  (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9))))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_035_468 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (6)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_468
  counts := ![(.branch 23 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 27 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 42 (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 47 (.leaf (19)) (.leaf (20))))))),
  (.branch 21 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 30 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.branch 29 (.leaf (-16)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (-6))) (.branch 41 (.leaf (-9)) (.leaf (-11)))),
  (.branch 24 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-12)) (.leaf (-13)))),
  (.branch 12 (.leaf (0)) (.branch 43 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 35 (.branch 30 (.leaf (-18)) (.leaf (-17))) (.branch 40 (.leaf (-16)) (.branch 45 (.leaf (-15)) (.leaf (-11))))),
  (.branch 41 (.branch 31 (.leaf (-18)) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 46 (.leaf (-15)) (.branch 47 (.leaf (-10)) (.leaf (-5))))),
  (.branch 34 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.leaf (-11)) (.branch 43 (.leaf (-10)) (.leaf (-9)))) (.branch 46 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 47 (.leaf (-6)) (.leaf (-5))))),
  (.branch 25 (.leaf (-2)) (.branch 39 (.leaf (-1)) (.leaf (0)))),
  (.branch 41 (.branch 38 (.branch 20 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))) (.branch 39 (.leaf (-10)) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_035_469 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (3))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (2)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (2)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (5)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (4)) (.branch 44 (.leaf (6)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_469
  counts := ![(.branch 21 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 27 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 31 (.leaf (9)) (.leaf (10)))) (.branch 41 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 40 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 17 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-13)))) (.branch 27 (.leaf (-15)) (.branch 41 (.leaf (-18)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 33 (.leaf (-8)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 46 (.branch 42 (.leaf (-20)) (.leaf (-19))) (.branch 47 (.leaf (-16)) (.leaf (-13)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.leaf (-12)) (.branch 41 (.leaf (-11)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 21 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_035_470 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (2)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_470
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 29 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 41 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 45 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_035_471 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (4)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (5)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (4))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (6)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (5)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_471
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 24 (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 36 (.branch 29 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 41 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 48 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-1)) (.leaf (-2)))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.leaf (-1)) (.leaf (0))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 40 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_035_472 : CycleWitness 7 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (5))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_472
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))) (.branch 44 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_035 : Fin 20 → CycleWitness 7 := ![witnessD7_035_453, witnessD7_035_454, witnessD7_035_455, witnessD7_035_456, witnessD7_035_457, witnessD7_035_458, witnessD7_035_459, witnessD7_035_460, witnessD7_035_461, witnessD7_035_462, witnessD7_035_463, witnessD7_035_464, witnessD7_035_465, witnessD7_035_466, witnessD7_035_467, witnessD7_035_468, witnessD7_035_469, witnessD7_035_470, witnessD7_035_471, witnessD7_035_472]
end RealPinwheel.FiveSixths


