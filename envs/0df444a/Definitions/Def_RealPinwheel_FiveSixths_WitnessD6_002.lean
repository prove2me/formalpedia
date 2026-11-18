-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_002
-- name    : RealPinwheel_FiveSixths_WitnessD6_002
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:07:02.903782+00:00
-- url     : https://prove2.me/theorems/1906c938-aae3-4c33-b170-ecfb612e76c5
-- title:
--   Exact witness block D6_002
-- statement:
--   These exact witnesses represent words 36 through 56 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 36–56; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_002_35 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (0))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (5)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_35
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 18 (.leaf (9)) (.branch 20 (.leaf (10)) (.leaf (11)))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (12)) (.branch 26 (.leaf (13)) (.leaf (14)))) (.branch 30 (.leaf (15)) (.branch 32 (.leaf (16)) (.leaf (17))))) (.branch 40 (.branch 37 (.leaf (18)) (.branch 38 (.leaf (19)) (.leaf (20)))) (.branch 44 (.branch 42 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24))))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 45 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-27))),
  (.branch 45 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 24 (.branch 22 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_002_36 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (5))))) (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_36
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 23 (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))) (.branch 35 (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))) (.branch 43 (.branch 39 (.leaf (9)) (.leaf (10))) (.branch 47 (.leaf (11)) (.leaf (12)))))),
  (.branch 24 (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-30))),
  (.branch 42 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 39 (.branch 34 (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))))) (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 25 (.branch 21 (.branch 19 (.leaf (-30)) (.branch 20 (.leaf (-29)) (.leaf (-28)))) (.branch 23 (.branch 22 (.leaf (-27)) (.leaf (-26))) (.branch 24 (.leaf (-25)) (.leaf (-24))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-23)) (.leaf (-22))) (.branch 28 (.leaf (-21)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-19)) (.leaf (-18))) (.branch 32 (.leaf (-17)) (.leaf (-16)))))) (.branch 40 (.branch 36 (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_002_37 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (5))))) (.branch 33 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (3)) (.leaf (0)))))) (.branch 41 (.branch 38 (.branch 37 (.leaf (1)) (.leaf (4))) (.branch 39 (.leaf (0)) (.branch 40 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (5)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_37
  counts := ![(.branch 22 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))) (.branch 33 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 42 (.branch 36 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17)))) (.branch 43 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 37 (.branch 31 (.branch 27 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 48 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 19 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 9 (.leaf (-10)) (.leaf (-13)))) (.branch 33 (.branch 26 (.leaf (-15)) (.leaf (-18))) (.branch 43 (.leaf (-21)) (.leaf (-23))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-10)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.branch 45 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 44 (.leaf (-23)) (.branch 47 (.leaf (-22)) (.leaf (-19)))),
  (.branch 38 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (0)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 42 (.branch 39 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_002_38 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1))))))) (.branch 36 (.branch 31 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (0))))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 43 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (2))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 44 (.leaf (5)) (.leaf (0))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (0)) (.leaf (1))))))))
  code := certificateD6_38
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))) (.branch 19 (.branch 18 (.leaf (10)) (.leaf (11))) (.branch 21 (.leaf (12)) (.leaf (13)))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (15)) (.leaf (16)))) (.branch 31 (.branch 30 (.leaf (17)) (.leaf (18))) (.branch 33 (.leaf (19)) (.leaf (20))))) (.branch 42 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 40 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 43 (.leaf (25)) (.leaf (26))) (.branch 47 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 36 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 48 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-28))),
  (.branch 44 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 44 (.leaf (-11)) (.branch 46 (.leaf (-9)) (.leaf (-7)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (-16)) (.leaf (-15))) (.branch 35 (.leaf (-14)) (.leaf (-13)))) (.branch 38 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 39 (.leaf (-10)) (.leaf (-9))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 27 (.branch 23 (.branch 21 (.leaf (-28)) (.branch 22 (.leaf (-27)) (.leaf (-26)))) (.branch 25 (.branch 24 (.leaf (-25)) (.leaf (-24))) (.branch 26 (.leaf (-23)) (.leaf (-22))))) (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15)))))) (.branch 41 (.branch 37 (.branch 35 (.leaf (-14)) (.branch 36 (.leaf (-13)) (.leaf (-12)))) (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8))))) (.branch 44 (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_002_39 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (1))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 38 (.leaf (0)) (.leaf (4))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (5)) (.leaf (1))))))))
  code := certificateD6_39
  counts := ![(.branch 22 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))) (.branch 34 (.branch 26 (.branch 25 (.leaf (10)) (.leaf (11))) (.branch 29 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20))))))),
  (.branch 24 (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 36 (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))) (.branch 45 (.branch 40 (.leaf (9)) (.leaf (10))) (.branch 48 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 47 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))) (.branch 26 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-9))))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 39 (.leaf (-9)) (.branch 47 (.leaf (-8)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_002_40 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_40
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 22 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.branch 24 (.leaf (0)) (.leaf (-24))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (-24)) (.branch 26 (.leaf (-23)) (.leaf (-22)))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19))))) (.branch 33 (.branch 31 (.leaf (-18)) (.branch 32 (.leaf (-17)) (.leaf (-16)))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-10)))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_002_41 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (0)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (0)))) (.branch 46 (.leaf (3)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_41
  counts := ![(.branch 23 (.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))) (.branch 35 (.branch 29 (.branch 25 (.leaf (12)) (.branch 27 (.leaf (13)) (.leaf (14)))) (.branch 31 (.leaf (15)) (.branch 33 (.leaf (16)) (.leaf (17))))) (.branch 41 (.branch 37 (.leaf (18)) (.branch 39 (.leaf (19)) (.leaf (20)))) (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 46 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-8)))) (.branch 30 (.leaf (-10)) (.branch 42 (.leaf (-12)) (.leaf (-14))))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 46 (.leaf (-11)) (.branch 47 (.leaf (-10)) (.leaf (-9))))),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_002_42 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (2)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (2)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (0)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (2)) (.leaf (3)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (4)) (.branch 41 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (2)) (.leaf (5))))))))
  code := certificateD6_42
  counts := ![(.branch 21 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 45 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 41 (.leaf (6)) (.branch 47 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1)))),
  (.branch 44 (.branch 42 (.branch 41 (.leaf (-8)) (.leaf (-7))) (.branch 43 (.leaf (-6)) (.leaf (-5)))) (.branch 46 (.branch 45 (.leaf (-4)) (.leaf (-3))) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_002_43 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (0)) (.branch 32 (.leaf (5)) (.leaf (1)))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3))))) (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 46 (.leaf (0)) (.branch 47 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_43
  counts := ![(.branch 22 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 34 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 31 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 43 (.leaf (14)) (.branch 46 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 29 (.branch 26 (.leaf (8)) (.leaf (9))) (.branch 33 (.leaf (10)) (.leaf (11)))) (.branch 41 (.branch 38 (.leaf (12)) (.leaf (13))) (.branch 45 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 20 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 44 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.branch 39 (.leaf (-8)) (.leaf (-9)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 45 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-1)) (.leaf (0)))]
def witnessD6_002_44 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (3)) (.leaf (1))))) (.branch 33 (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (5)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (4)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1))))) (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (0)) (.leaf (2)))) (.branch 46 (.leaf (1)) (.branch 47 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_44
  counts := ![(.branch 23 (.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 32 (.leaf (10)) (.leaf (11)))) (.branch 40 (.branch 37 (.leaf (12)) (.leaf (13))) (.branch 44 (.leaf (14)) (.branch 47 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 34 (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))) (.branch 42 (.branch 38 (.leaf (9)) (.leaf (10))) (.branch 46 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 27 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 45 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 48 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (-8)) (.leaf (-10)))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (-8))) (.branch 39 (.leaf (-10)) (.leaf (-12)))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 47 (.leaf (-2)) (.leaf (-1))),
  (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))),
  (.branch 45 (.branch 30 (.leaf (-10)) (.branch 44 (.leaf (-9)) (.leaf (-8)))) (.branch 46 (.leaf (-7)) (.branch 47 (.leaf (-6)) (.leaf (-5))))),
  (.branch 43 (.branch 41 (.branch 40 (.leaf (-12)) (.leaf (-11))) (.branch 42 (.leaf (-10)) (.leaf (-9)))) (.branch 45 (.branch 44 (.leaf (-8)) (.leaf (-7))) (.branch 46 (.leaf (-6)) (.branch 47 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 16 (.leaf (-2)) (.branch 34 (.leaf (-1)) (.leaf (0))))]
def witnessD6_002_45 : CycleWitness 6 where
  length := 48
  word := (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (2))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (3)))) (.branch 28 (.leaf (0)) (.branch 29 (.leaf (2)) (.leaf (5))))) (.branch 33 (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (2)))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (1)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (1)) (.leaf (0))))) (.branch 45 (.branch 43 (.leaf (2)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_45
  counts := ![(.branch 21 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 28 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 42 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 23 (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 31 (.branch 26 (.leaf (7)) (.leaf (8))) (.branch 34 (.leaf (9)) (.leaf (10)))) (.branch 44 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 47 (.leaf (13)) (.leaf (14)))))),
  (.branch 24 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))) (.branch 38 (.branch 29 (.leaf (5)) (.branch 33 (.leaf (6)) (.leaf (7)))) (.branch 43 (.leaf (8)) (.branch 48 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.branch 23 (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))) (.branch 36 (.branch 26 (.leaf (-5)) (.leaf (-6))) (.branch 47 (.leaf (-8)) (.leaf (-9))))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.branch 37 (.leaf (-10)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 46 (.leaf (-21)) (.branch 47 (.leaf (-14)) (.leaf (-7)))),
  (.leaf (-9)),
  (.branch 39 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 44 (.leaf (-1)) (.leaf (0)))),
  (.branch 43 (.branch 41 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 42 (.leaf (-7)) (.leaf (-6)))) (.branch 45 (.branch 44 (.leaf (-5)) (.leaf (-4))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))) (.branch 45 (.branch 43 (.leaf (-6)) (.branch 44 (.leaf (-5)) (.leaf (-4)))) (.branch 46 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 47 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_002_46 : CycleWitness 6 where
  length := 46
  word := (.branch 23 (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (2))) (.branch 9 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (4)) (.leaf (1))))))) (.branch 35 (.branch 29 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.branch 28 (.leaf (3)) (.leaf (0))))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 36 (.leaf (1)) (.leaf (4))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (3)) (.leaf (2))))) (.branch 43 (.branch 41 (.leaf (1)) (.leaf (0))) (.branch 44 (.leaf (2)) (.branch 45 (.leaf (5)) (.leaf (1))))))))
  code := certificateD6_46
  counts := ![(.branch 20 (.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 25 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 42 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))))),
  (.branch 23 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 36 (.branch 27 (.leaf (5)) (.branch 32 (.leaf (6)) (.leaf (7)))) (.branch 41 (.leaf (8)) (.branch 46 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 35 (.branch 26 (.leaf (5)) (.branch 31 (.leaf (6)) (.leaf (7)))) (.branch 40 (.leaf (8)) (.branch 44 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 30 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 45 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-10)) (.leaf (-13)))) (.branch 34 (.branch 25 (.leaf (-16)) (.leaf (-20))) (.branch 43 (.leaf (-23)) (.leaf (-26))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-8))) (.branch 21 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-13)) (.leaf (-14)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-25))) (.branch 37 (.leaf (-26)) (.leaf (-27)))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 44 (.leaf (-26)) (.branch 45 (.leaf (-24)) (.leaf (-22)))),
  (.branch 37 (.leaf (-4)) (.branch 42 (.leaf (-2)) (.leaf (0)))),
  (.branch 45 (.leaf (-10)) (.leaf (-5))),
  (.branch 42 (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-12)) (.leaf (-10)))) (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-27)) (.leaf (-24))) (.branch 40 (.leaf (-21)) (.leaf (-18)))) (.branch 43 (.branch 42 (.leaf (-15)) (.leaf (-12))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 15 (.leaf (-4)) (.leaf (-3)))]
def witnessD6_002_47 : CycleWitness 6 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (3)) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 21 (.leaf (1)) (.branch 22 (.leaf (0)) (.leaf (4))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (3)) (.leaf (0)))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (1)) (.leaf (0)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1)))) (.branch 38 (.leaf (4)) (.branch 39 (.leaf (0)) (.leaf (1))))) (.branch 43 (.branch 41 (.leaf (3)) (.branch 42 (.leaf (0)) (.leaf (2)))) (.branch 44 (.leaf (1)) (.branch 45 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_47
  counts := ![(.branch 22 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))) (.branch 34 (.branch 26 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.branch 31 (.leaf (12)) (.leaf (13))))) (.branch 39 (.branch 36 (.leaf (14)) (.leaf (15))) (.branch 42 (.leaf (16)) (.branch 45 (.leaf (17)) (.leaf (18))))))),
  (.branch 21 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 40 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 44 (.leaf (11)) (.leaf (12)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 43 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))) (.branch 26 (.leaf (-9)) (.branch 28 (.leaf (-10)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (-7))) (.branch 38 (.leaf (-9)) (.leaf (-10)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.branch 37 (.leaf (-12)) (.leaf (-11))) (.branch 43 (.leaf (-10)) (.leaf (-9)))),
  (.branch 41 (.leaf (-13)) (.branch 45 (.leaf (-12)) (.leaf (-6)))),
  (.branch 36 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 43 (.branch 42 (.leaf (-10)) (.leaf (-8))) (.branch 44 (.leaf (-6)) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 42 (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))) (.branch 44 (.branch 43 (.leaf (-6)) (.leaf (-5))) (.branch 45 (.leaf (-4)) (.leaf (-3))))),
  (.branch 16 (.leaf (-1)) (.leaf (0)))]
def witnessD6_002_48 : CycleWitness 6 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (5)) (.leaf (1)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (3)) (.leaf (4)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (5))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (4)) (.leaf (1)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (2)) (.leaf (0))))) (.branch 43 (.branch 41 (.leaf (1)) (.branch 42 (.leaf (3)) (.leaf (5)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_48
  counts := ![(.branch 21 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))) (.branch 33 (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))) (.branch 41 (.branch 37 (.leaf (9)) (.leaf (10))) (.branch 45 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 46 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 17 (.leaf (-3)) (.branch 40 (.leaf (-4)) (.leaf (-5))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-31)) (.leaf (-32)))),
  (.branch 28 (.branch 13 (.leaf (0)) (.leaf (-7))) (.branch 43 (.leaf (-8)) (.leaf (-9))))]
  high := ![(.branch 41 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))),
  (.branch 34 (.branch 26 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-9)))) (.branch 38 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.branch 40 (.leaf (-3)) (.leaf (-2))) (.branch 42 (.leaf (-1)) (.leaf (0)))),
  (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 37 (.branch 21 (.leaf (-32)) (.leaf (-30))) (.branch 38 (.leaf (-27)) (.branch 39 (.leaf (-24)) (.leaf (-21))))) (.branch 43 (.branch 41 (.leaf (-18)) (.branch 42 (.leaf (-15)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))]
def witnessD6_002_49 : CycleWitness 6 where
  length := 46
  word := (.branch 23 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (5)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (4))))))) (.branch 34 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (3))))) (.branch 31 (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (5)))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2)))))) (.branch 40 (.branch 37 (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (4)))) (.branch 38 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (3))))) (.branch 43 (.branch 41 (.leaf (0)) (.branch 42 (.leaf (2)) (.leaf (1)))) (.branch 44 (.leaf (0)) (.branch 45 (.leaf (1)) (.leaf (5))))))))
  code := certificateD6_49
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))) (.branch 36 (.branch 29 (.branch 25 (.leaf (7)) (.leaf (8))) (.branch 32 (.leaf (9)) (.leaf (10)))) (.branch 43 (.branch 39 (.leaf (11)) (.leaf (12))) (.branch 45 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 34 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 40 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 31 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-15)) (.leaf (-19)))),
  (.branch 22 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 25 (.leaf (-9)) (.branch 45 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 23 (.branch 8 (.leaf (0)) (.leaf (-8))) (.branch 37 (.leaf (-9)) (.leaf (-11)))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 39 (.branch 36 (.leaf (-19)) (.leaf (-18))) (.branch 42 (.leaf (-17)) (.branch 45 (.leaf (-16)) (.leaf (-8))))),
  (.leaf (-13)),
  (.branch 43 (.branch 27 (.leaf (-14)) (.branch 35 (.leaf (-13)) (.leaf (-12)))) (.branch 44 (.leaf (-9)) (.branch 45 (.leaf (-6)) (.leaf (-3))))),
  (.branch 42 (.branch 29 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-10)))) (.branch 44 (.branch 43 (.leaf (-8)) (.leaf (-6))) (.branch 45 (.leaf (-4)) (.leaf (-2))))),
  (.branch 41 (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.leaf (-8)))) (.branch 43 (.branch 42 (.leaf (-7)) (.leaf (-6))) (.branch 44 (.leaf (-5)) (.branch 45 (.leaf (-4)) (.leaf (-3)))))),
  (.branch 15 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0))))]
def witnessD6_002_50 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4)))))) (.branch 33 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 42 (.branch 41 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_50
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (5)) (.leaf (6))))) (.branch 15 (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))) (.branch 18 (.branch 16 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13)))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (14)) (.branch 24 (.leaf (15)) (.leaf (16)))) (.branch 29 (.branch 27 (.leaf (17)) (.leaf (18))) (.branch 30 (.leaf (19)) (.leaf (20))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (21)) (.leaf (22))) (.branch 37 (.leaf (23)) (.leaf (24)))) (.branch 41 (.branch 40 (.leaf (25)) (.leaf (26))) (.branch 43 (.leaf (27)) (.leaf (28))))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 39 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-8)) (.branch 8 (.leaf (-9)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 22 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 42 (.leaf (-10)) (.leaf (-7))),
  (.branch 37 (.leaf (-5)) (.branch 43 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-22)) (.leaf (-21))) (.branch 25 (.leaf (-20)) (.branch 26 (.leaf (-19)) (.leaf (-18))))) (.branch 30 (.branch 28 (.leaf (-17)) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_002_51 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (0))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (1)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (4))) (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 40 (.leaf (1)) (.leaf (0))) (.branch 42 (.leaf (3)) (.branch 43 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_51
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 17 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (12)) (.branch 24 (.leaf (13)) (.leaf (14)))) (.branch 28 (.leaf (15)) (.branch 30 (.leaf (16)) (.leaf (17))))) (.branch 37 (.branch 34 (.leaf (18)) (.branch 35 (.leaf (19)) (.leaf (20)))) (.branch 41 (.branch 39 (.leaf (21)) (.leaf (22))) (.branch 43 (.leaf (23)) (.leaf (24))))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 29 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 44 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 36 (.leaf (-23)) (.leaf (-24)))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 38 (.branch 36 (.leaf (-10)) (.leaf (-9))) (.branch 40 (.leaf (-8)) (.branch 42 (.leaf (-7)) (.leaf (-6))))),
  (.branch 41 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 42 (.leaf (-9)) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))),
  (.branch 43 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.branch 38 (.branch 37 (.leaf (-24)) (.leaf (-21))) (.branch 39 (.leaf (-18)) (.leaf (-15)))) (.branch 42 (.branch 41 (.leaf (-12)) (.leaf (-9))) (.branch 43 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))]
def witnessD6_002_52 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (1))))))) (.branch 33 (.branch 28 (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1)))))) (.branch 39 (.branch 36 (.branch 35 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (5)) (.branch 38 (.leaf (0)) (.leaf (1))))) (.branch 41 (.branch 40 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_52
  counts := ![(.branch 20 (.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))) (.branch 31 (.branch 24 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 35 (.leaf (16)) (.leaf (17)))) (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20))))))),
  (.branch 22 (.branch 11 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 28 (.branch 25 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 39 (.branch 36 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.branch 44 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 43 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))) (.branch 24 (.leaf (-11)) (.branch 35 (.leaf (-12)) (.leaf (-13))))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 15 (.leaf (0)) (.leaf (-29))),
  (.branch 37 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 36 (.leaf (-13)) (.branch 43 (.leaf (-12)) (.leaf (-8)))),
  (.branch 42 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 35 (.branch 30 (.branch 28 (.branch 27 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))))) (.branch 39 (.branch 37 (.branch 36 (.leaf (-9)) (.leaf (-8))) (.branch 38 (.leaf (-7)) (.leaf (-6)))) (.branch 41 (.branch 40 (.leaf (-5)) (.leaf (-4))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 22 (.branch 18 (.branch 16 (.leaf (-29)) (.branch 17 (.leaf (-28)) (.leaf (-27)))) (.branch 20 (.branch 19 (.leaf (-26)) (.leaf (-25))) (.branch 21 (.leaf (-24)) (.leaf (-23))))) (.branch 25 (.branch 23 (.leaf (-22)) (.branch 24 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.branch 26 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-17)) (.leaf (-16)))))) (.branch 36 (.branch 32 (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))) (.branch 34 (.branch 33 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-9))))) (.branch 40 (.branch 38 (.branch 37 (.leaf (-8)) (.leaf (-7))) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_002_53 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (2)) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (3)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (2)) (.branch 40 (.leaf (0)) (.leaf (1)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (5)) (.leaf (2))))))))
  code := certificateD6_53
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 40 (.leaf (18)) (.branch 42 (.leaf (19)) (.leaf (20))))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 24 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 22 (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 43 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))) (.branch 26 (.leaf (-5)) (.branch 37 (.leaf (-6)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-23))),
  (.branch 43 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 43 (.leaf (-10)) (.leaf (-5))),
  (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf (-23)) (.leaf (-22))) (.branch 24 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19))))) (.branch 29 (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 30 (.leaf (-15)) (.branch 31 (.leaf (-14)) (.leaf (-13)))))) (.branch 38 (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-10)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD6_002_54 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))) (.branch 30 (.branch 28 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (3)))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))) (.branch 41 (.branch 39 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (5)))) (.branch 42 (.leaf (0)) (.branch 43 (.leaf (1)) (.leaf (2))))))))
  code := certificateD6_54
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 25 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 28 (.leaf (10)) (.leaf (11)))) (.branch 36 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 39 (.leaf (14)) (.branch 42 (.leaf (15)) (.leaf (16))))))),
  (.branch 21 (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.branch 43 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.branch 44 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-25))),
  (.branch 41 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 40 (.branch 37 (.leaf (-10)) (.leaf (-9))) (.branch 43 (.leaf (-8)) (.leaf (-4)))),
  (.branch 38 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))),
  (.branch 39 (.leaf (-1)) (.leaf (0))),
  (.branch 37 (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))) (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 20 (.leaf (-25)) (.branch 21 (.leaf (-24)) (.leaf (-23)))) (.branch 23 (.leaf (-22)) (.branch 24 (.leaf (-21)) (.leaf (-20))))) (.branch 28 (.branch 26 (.leaf (-19)) (.branch 27 (.leaf (-18)) (.leaf (-17)))) (.branch 29 (.leaf (-16)) (.branch 30 (.leaf (-15)) (.leaf (-14)))))) (.branch 37 (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-9)) (.leaf (-8))))) (.branch 40 (.branch 38 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5)))) (.branch 42 (.branch 41 (.leaf (-4)) (.leaf (-3))) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_002_55 : CycleWitness 6 where
  length := 44
  word := (.branch 22 (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (2)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4))))))) (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.leaf (1)) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (3)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (0))))) (.branch 41 (.branch 39 (.leaf (1)) (.branch 40 (.leaf (0)) (.leaf (2)))) (.branch 42 (.leaf (1)) (.branch 43 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_55
  counts := ![(.branch 21 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))) (.branch 32 (.branch 25 (.branch 23 (.leaf (10)) (.leaf (11))) (.branch 27 (.leaf (12)) (.branch 29 (.leaf (13)) (.leaf (14))))) (.branch 38 (.branch 34 (.leaf (15)) (.branch 36 (.leaf (16)) (.leaf (17)))) (.branch 40 (.leaf (18)) (.branch 43 (.leaf (19)) (.leaf (20))))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))) (.branch 31 (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))) (.branch 39 (.branch 35 (.leaf (9)) (.leaf (10))) (.branch 42 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 44 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 7 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))) (.branch 30 (.leaf (-5)) (.branch 41 (.leaf (-6)) (.leaf (-7))))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.branch 22 (.leaf (0)) (.leaf (-22))),
  (.leaf (0))]
  high := ![(.branch 41 (.leaf (-9)) (.leaf (-5))),
  (.branch 43 (.leaf (-6)) (.leaf (-3))),
  (.branch 42 (.leaf (-7)) (.branch 43 (.leaf (-6)) (.leaf (-5)))),
  (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 27 (.branch 24 (.branch 23 (.leaf (-22)) (.leaf (-21))) (.branch 25 (.leaf (-20)) (.branch 26 (.leaf (-19)) (.leaf (-18))))) (.branch 30 (.branch 28 (.leaf (-17)) (.branch 29 (.leaf (-16)) (.leaf (-15)))) (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-13)) (.leaf (-12)))))) (.branch 38 (.branch 35 (.branch 34 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7))))) (.branch 41 (.branch 39 (.leaf (-6)) (.branch 40 (.leaf (-5)) (.leaf (-4)))) (.branch 42 (.leaf (-3)) (.branch 43 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_002 : Fin 21 → CycleWitness 6 := ![witnessD6_002_35, witnessD6_002_36, witnessD6_002_37, witnessD6_002_38, witnessD6_002_39, witnessD6_002_40, witnessD6_002_41, witnessD6_002_42, witnessD6_002_43, witnessD6_002_44, witnessD6_002_45, witnessD6_002_46, witnessD6_002_47, witnessD6_002_48, witnessD6_002_49, witnessD6_002_50, witnessD6_002_51, witnessD6_002_52, witnessD6_002_53, witnessD6_002_54, witnessD6_002_55]
end RealPinwheel.FiveSixths


