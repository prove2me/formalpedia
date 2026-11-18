-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_027
-- name    : RealPinwheel_FiveSixths_WitnessD7_027
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:32.239609+00:00
-- url     : https://prove2.me/theorems/999b065a-1d42-4100-a029-c9a106fa2b42
-- title:
--   Exact witness block D7_027
-- statement:
--   These exact witnesses represent words 307 through 323 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 307–323; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_027_306 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.leaf (0)) (.branch 24 (.leaf (5)) (.leaf (0)))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (3))))))) (.branch 42 (.branch 36 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (2)) (.leaf (0)))) (.branch 33 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 50 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 49 (.leaf (0)) (.leaf (2))))) (.branch 53 (.branch 51 (.leaf (0)) (.branch 52 (.leaf (6)) (.leaf (0)))) (.branch 54 (.leaf (1)) (.branch 55 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_306
  counts := ![(.branch 27 (.branch 13 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))) (.branch 20 (.branch 16 (.branch 15 (.leaf (8)) (.leaf (9))) (.branch 18 (.leaf (10)) (.leaf (11)))) (.branch 23 (.branch 21 (.leaf (12)) (.leaf (13))) (.branch 25 (.leaf (14)) (.leaf (15)))))) (.branch 41 (.branch 34 (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 32 (.leaf (18)) (.leaf (19)))) (.branch 37 (.branch 35 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (24)) (.leaf (25))) (.branch 46 (.leaf (26)) (.leaf (27)))) (.branch 51 (.branch 49 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (30)) (.branch 55 (.leaf (31)) (.leaf (32)))))))),
  (.branch 26 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 40 (.branch 33 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 54 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 31 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))) (.branch 45 (.branch 36 (.leaf (3)) (.leaf (4))) (.branch 56 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2)))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 52 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 22 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 31 (.leaf (-8)) (.branch 50 (.leaf (-9)) (.leaf (-10))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (-2))) (.branch 36 (.leaf (-3)) (.branch 45 (.leaf (-4)) (.leaf (-5))))),
  (.branch 10 (.leaf (0)) (.leaf (-18))),
  (.branch 24 (.leaf (0)) (.leaf (-32))),
  (.branch 52 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 52 (.branch 50 (.leaf (-7)) (.leaf (-6))) (.branch 54 (.leaf (-5)) (.leaf (-4)))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.branch 51 (.leaf (-10)) (.branch 52 (.leaf (-9)) (.leaf (-8)))) (.branch 54 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5))))),
  (.branch 48 (.branch 46 (.leaf (-5)) (.branch 47 (.leaf (-4)) (.leaf (-3)))) (.branch 49 (.leaf (-2)) (.branch 50 (.leaf (-1)) (.leaf (0))))),
  (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_027_307 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (1)))))) (.branch 21 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (5)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (1))))))) (.branch 42 (.branch 35 (.branch 32 (.branch 30 (.leaf (0)) (.branch 31 (.leaf (3)) (.leaf (0)))) (.branch 33 (.leaf (1)) (.branch 34 (.leaf (0)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (1)))))) (.branch 49 (.branch 46 (.branch 44 (.leaf (0)) (.branch 45 (.leaf (3)) (.leaf (0)))) (.branch 47 (.leaf (1)) (.branch 48 (.leaf (0)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_307
  counts := ![(.branch 26 (.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))) (.branch 22 (.branch 20 (.leaf (10)) (.leaf (11))) (.branch 24 (.leaf (12)) (.leaf (13)))))) (.branch 40 (.branch 32 (.branch 29 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16)))) (.branch 36 (.branch 34 (.leaf (17)) (.leaf (18))) (.branch 38 (.leaf (19)) (.leaf (20))))) (.branch 48 (.branch 44 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 46 (.leaf (23)) (.leaf (24)))) (.branch 52 (.branch 50 (.leaf (25)) (.leaf (26))) (.branch 54 (.leaf (27)) (.leaf (28))))))),
  (.branch 28 (.branch 14 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 47 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 35 (.leaf (4)) (.leaf (5))) (.branch 49 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 45 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 52 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_027_308 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (5)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_308
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 48 (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20)))) (.branch 53 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 55 (.leaf (23)) (.leaf (24))))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-1))) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-42))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.branch 42 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 55 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-42)) (.leaf (-41))) (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38))))) (.branch 21 (.branch 20 (.leaf (-37)) (.leaf (-36))) (.branch 22 (.leaf (-35)) (.branch 23 (.leaf (-34)) (.leaf (-33)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 32 (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-26)) (.leaf (-25)))) (.branch 33 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-22))))))) (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_027_309 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (2))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (6))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_309
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 20 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 23 (.leaf (9)) (.branch 25 (.leaf (10)) (.leaf (11)))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (12)) (.branch 32 (.leaf (13)) (.leaf (14)))) (.branch 37 (.leaf (15)) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 48 (.branch 44 (.leaf (18)) (.branch 46 (.leaf (19)) (.leaf (20)))) (.branch 53 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 55 (.leaf (23)) (.leaf (24))))))),
  (.branch 7 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.branch 56 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 49 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-1))) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-21))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.branch 21 (.leaf (0)) (.leaf (-35))),
  (.branch 49 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 55 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.branch 45 (.branch 40 (.branch 37 (.branch 36 (.leaf (-21)) (.leaf (-20))) (.branch 38 (.leaf (-19)) (.branch 39 (.leaf (-18)) (.leaf (-17))))) (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0)),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-35)) (.leaf (-34))) (.branch 24 (.leaf (-33)) (.leaf (-32)))) (.branch 27 (.branch 26 (.leaf (-31)) (.leaf (-30))) (.branch 28 (.leaf (-29)) (.leaf (-28))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_027_310 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (5)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_310
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 39 (.leaf (0)) (.leaf (1))),
  (.branch 53 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))) (.branch 36 (.leaf (-3)) (.branch 50 (.leaf (-4)) (.leaf (-5))))),
  (.branch 11 (.leaf (0)) (.leaf (-45))),
  (.branch 25 (.leaf (0)) (.leaf (-31))),
  (.branch 39 (.leaf (0)) (.leaf (-17))),
  (.branch 53 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 50 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 51 (.leaf (-5)) (.branch 52 (.leaf (-4)) (.leaf (-3)))) (.branch 54 (.leaf (-2)) (.branch 55 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-45)) (.leaf (-44))) (.branch 14 (.leaf (-43)) (.branch 15 (.leaf (-42)) (.leaf (-41))))) (.branch 19 (.branch 17 (.leaf (-40)) (.branch 18 (.leaf (-39)) (.leaf (-38)))) (.branch 20 (.leaf (-37)) (.branch 21 (.leaf (-36)) (.leaf (-35)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-34)) (.leaf (-33))) (.branch 25 (.leaf (-32)) (.branch 26 (.leaf (-31)) (.leaf (-30))))) (.branch 30 (.branch 28 (.leaf (-29)) (.branch 29 (.leaf (-28)) (.leaf (-27)))) (.branch 31 (.leaf (-26)) (.branch 32 (.leaf (-25)) (.leaf (-24))))))) (.branch 44 (.branch 38 (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))) (.branch 41 (.branch 39 (.leaf (-18)) (.branch 40 (.leaf (-17)) (.leaf (-16)))) (.branch 42 (.leaf (-15)) (.branch 43 (.leaf (-14)) (.leaf (-13)))))) (.branch 50 (.branch 47 (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 40 (.branch 32 (.branch 28 (.branch 26 (.leaf (-31)) (.branch 27 (.leaf (-30)) (.leaf (-29)))) (.branch 30 (.branch 29 (.leaf (-28)) (.leaf (-27))) (.branch 31 (.leaf (-26)) (.leaf (-25))))) (.branch 36 (.branch 34 (.branch 33 (.leaf (-24)) (.leaf (-23))) (.branch 35 (.leaf (-22)) (.leaf (-21)))) (.branch 38 (.branch 37 (.leaf (-20)) (.leaf (-19))) (.branch 39 (.leaf (-18)) (.leaf (-17)))))) (.branch 48 (.branch 44 (.branch 42 (.branch 41 (.leaf (-16)) (.leaf (-15))) (.branch 43 (.leaf (-14)) (.leaf (-13)))) (.branch 46 (.branch 45 (.leaf (-12)) (.leaf (-11))) (.branch 47 (.leaf (-10)) (.leaf (-9))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_027_311 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (6)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (3))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (4)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (5)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (3)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (6)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_311
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.branch 53 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-17))),
  (.branch 25 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 50 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 54 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 37 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 47 (.branch 43 (.branch 41 (.branch 40 (.leaf (-17)) (.leaf (-16))) (.branch 42 (.leaf (-15)) (.leaf (-14)))) (.branch 45 (.branch 44 (.leaf (-13)) (.leaf (-12))) (.branch 46 (.leaf (-11)) (.leaf (-10))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_027_312 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (4))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (3))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (4)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (3))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_312
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (-29)) (.leaf (-31)))),
  (.branch 18 (.leaf (0)) (.branch 55 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 55 (.leaf (-6)) (.leaf (-3))),
  (.branch 54 (.branch 49 (.leaf (-10)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.branch 42 (.leaf (-17)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 50 (.branch 47 (.branch 28 (.leaf (-31)) (.leaf (-30))) (.branch 48 (.leaf (-27)) (.branch 49 (.leaf (-24)) (.leaf (-21))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3))]
def witnessD7_027_313 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (0)) (.leaf (5))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (0)) (.leaf (1)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (4))) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (0))) (.branch 48 (.leaf (3)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (0)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_313
  counts := ![(.branch 27 (.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))) (.branch 19 (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))) (.branch 23 (.branch 21 (.leaf (10)) (.leaf (11))) (.branch 25 (.leaf (12)) (.leaf (13)))))) (.branch 41 (.branch 33 (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16)))) (.branch 37 (.branch 35 (.leaf (17)) (.leaf (18))) (.branch 39 (.leaf (19)) (.leaf (20))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (21)) (.leaf (22))) (.branch 47 (.leaf (23)) (.leaf (24)))) (.branch 53 (.branch 51 (.leaf (25)) (.leaf (26))) (.branch 55 (.leaf (27)) (.leaf (28))))))),
  (.branch 24 (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 38 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 52 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.leaf (-1)),
  (.branch 53 (.branch 45 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 54 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 37 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD7_027_314 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (3)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (4)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (3)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (2)) (.leaf (0))) (.branch 48 (.leaf (6)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_314
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 39 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 44 (.leaf (9)) (.leaf (10))) (.branch 53 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))) (.branch 42 (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))) (.branch 51 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 56 (.leaf (11)) (.leaf (12)))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 48 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-22))),
  (.branch 20 (.leaf (0)) (.leaf (-36))),
  (.branch 48 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 55 (.leaf (-6)) (.leaf (-3))),
  (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 47 (.leaf (-2)) (.branch 52 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 45 (.branch 39 (.branch 36 (.branch 35 (.leaf (-22)) (.leaf (-21))) (.branch 37 (.leaf (-20)) (.branch 38 (.leaf (-19)) (.leaf (-18))))) (.branch 42 (.branch 40 (.leaf (-17)) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))))) (.branch 50 (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.branch 49 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 51 (.leaf (-6)) (.branch 52 (.leaf (-5)) (.leaf (-4)))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-36)) (.leaf (-35))) (.branch 23 (.leaf (-34)) (.leaf (-33)))) (.branch 26 (.branch 25 (.leaf (-32)) (.leaf (-31))) (.branch 27 (.leaf (-30)) (.branch 28 (.leaf (-29)) (.leaf (-28)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-26))) (.branch 32 (.leaf (-25)) (.leaf (-24)))) (.branch 35 (.branch 34 (.leaf (-23)) (.leaf (-22))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19))))))) (.branch 47 (.branch 42 (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))) (.branch 44 (.branch 43 (.leaf (-14)) (.leaf (-13))) (.branch 45 (.leaf (-12)) (.branch 46 (.leaf (-11)) (.leaf (-10)))))) (.branch 51 (.branch 49 (.branch 48 (.leaf (-9)) (.leaf (-8))) (.branch 50 (.leaf (-7)) (.leaf (-6)))) (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_027_315 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (3))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (5)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (6)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (3)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (1)) (.leaf (0))) (.branch 48 (.leaf (5)) (.leaf (2))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (4)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_315
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 22 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 36 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 50 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 25 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))) (.branch 41 (.branch 30 (.leaf (5)) (.branch 35 (.leaf (6)) (.leaf (7)))) (.branch 46 (.leaf (8)) (.branch 53 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 39 (.leaf (3)) (.branch 49 (.leaf (4)) (.leaf (5))))),
  (.branch 32 (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 44 (.leaf (3)) (.branch 55 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 18 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))) (.branch 35 (.leaf (-6)) (.branch 46 (.leaf (-7)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 49 (.leaf (-22)) (.leaf (-23)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 55 (.leaf (-6)) (.leaf (-3))),
  (.branch 54 (.branch 47 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 52 (.branch 50 (.leaf (-23)) (.branch 51 (.leaf (-20)) (.leaf (-17)))) (.branch 54 (.branch 53 (.leaf (-14)) (.leaf (-11))) (.branch 55 (.leaf (-8)) (.leaf (-5))))),
  (.branch 33 (.leaf (-6)) (.leaf (-5))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_027_316 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (5))))))) (.branch 42 (.branch 34 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (2)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (4)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (2)) (.branch 47 (.leaf (1)) (.leaf (0))))) (.branch 51 (.branch 49 (.leaf (3)) (.branch 50 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_316
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 40 (.branch 31 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 43 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 27 (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))) (.branch 41 (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))) (.branch 50 (.branch 46 (.leaf (9)) (.leaf (10))) (.branch 55 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2)))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 56 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 39 (.branch 25 (.leaf (-5)) (.leaf (-7))) (.branch 53 (.leaf (-9)) (.leaf (-11))))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-14))),
  (.branch 28 (.leaf (0)) (.leaf (-28))),
  (.leaf (0))]
  high := ![(.branch 49 (.branch 46 (.leaf (-13)) (.leaf (-12))) (.branch 52 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 51 (.leaf (-4)) (.leaf (-3))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (-28)) (.branch 30 (.leaf (-27)) (.leaf (-26)))) (.branch 33 (.branch 32 (.leaf (-25)) (.leaf (-24))) (.branch 34 (.leaf (-23)) (.leaf (-22))))) (.branch 38 (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-20)) (.leaf (-19)))) (.branch 40 (.branch 39 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-15)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (-14)) (.branch 44 (.leaf (-13)) (.leaf (-12)))) (.branch 47 (.branch 46 (.leaf (-11)) (.leaf (-10))) (.branch 48 (.leaf (-9)) (.leaf (-8))))) (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_027_317 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (1)) (.leaf (0))))) (.branch 23 (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (4))))))) (.branch 42 (.branch 34 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (0))))) (.branch 37 (.branch 35 (.leaf (3)) (.branch 36 (.leaf (6)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (4)))))) (.branch 48 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 46 (.leaf (5)) (.branch 47 (.leaf (1)) (.leaf (0))))) (.branch 51 (.branch 49 (.leaf (3)) (.branch 50 (.leaf (2)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (1)) (.leaf (0))) (.branch 55 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_317
  counts := ![(.branch 26 (.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 15 (.leaf (5)) (.leaf (6))) (.branch 20 (.leaf (7)) (.branch 23 (.leaf (8)) (.leaf (9)))))) (.branch 40 (.branch 31 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.branch 37 (.leaf (13)) (.leaf (14))))) (.branch 48 (.branch 43 (.leaf (15)) (.branch 45 (.leaf (16)) (.leaf (17)))) (.branch 51 (.leaf (18)) (.branch 54 (.leaf (19)) (.leaf (20))))))),
  (.branch 25 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 33 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 47 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 52 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 41 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.branch 49 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.branch 56 (.leaf (3)) (.leaf (4))))),
  (.branch 27 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))) (.branch 39 (.branch 25 (.leaf (-5)) (.leaf (-7))) (.branch 53 (.leaf (-9)) (.leaf (-11))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-32))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-2)) (.leaf (-4))))]
  high := ![(.branch 49 (.branch 46 (.leaf (-13)) (.leaf (-12))) (.branch 52 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-5))))),
  (.branch 54 (.leaf (-11)) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 50 (.leaf (-7)) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 50 (.branch 47 (.branch 9 (.leaf (-32)) (.branch 28 (.leaf (-31)) (.leaf (-30)))) (.branch 48 (.leaf (-27)) (.branch 49 (.leaf (-24)) (.leaf (-21))))) (.branch 53 (.branch 51 (.leaf (-18)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3)))]
def witnessD7_027_318 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (4))) (.branch 27 (.leaf (1)) (.leaf (5))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (3)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (1)) (.branch 37 (.leaf (6)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (1)) (.leaf (4))) (.branch 41 (.leaf (0)) (.leaf (2)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (1)) (.branch 44 (.leaf (0)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (0))) (.branch 48 (.leaf (3)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (0)) (.branch 51 (.leaf (2)) (.leaf (1)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (4))) (.branch 55 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_318
  counts := ![(.branch 25 (.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))) (.branch 41 (.branch 31 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.branch 38 (.leaf (12)) (.leaf (13))))) (.branch 47 (.branch 44 (.leaf (14)) (.leaf (15))) (.branch 50 (.leaf (16)) (.branch 53 (.leaf (17)) (.leaf (18))))))),
  (.branch 27 (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))) (.branch 43 (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.branch 39 (.leaf (12)) (.leaf (13))))) (.branch 49 (.branch 45 (.leaf (14)) (.leaf (15))) (.branch 52 (.leaf (16)) (.branch 55 (.leaf (17)) (.leaf (18))))))),
  (.branch 23 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 51 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 48 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 40 (.leaf (2)) (.branch 54 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 37 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 31 (.leaf (-26)) (.leaf (-27)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-9)) (.leaf (-10)))) (.branch 17 (.branch 11 (.leaf (-11)) (.leaf (-12))) (.branch 45 (.leaf (-14)) (.leaf (-15))))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.branch 46 (.leaf (-29)) (.leaf (-30)))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 54 (.branch 32 (.leaf (-27)) (.leaf (-26))) (.branch 55 (.leaf (-18)) (.leaf (-10)))),
  (.branch 46 (.leaf (-15)) (.leaf (-10))),
  (.branch 53 (.branch 33 (.leaf (-16)) (.branch 52 (.leaf (-15)) (.leaf (-12)))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3))))),
  (.branch 52 (.branch 50 (.branch 49 (.leaf (-8)) (.leaf (-7))) (.branch 51 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.branch 53 (.leaf (-4)) (.leaf (-3))) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 55 (.leaf (-2)) (.leaf (-1))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-30)) (.leaf (-27))) (.branch 49 (.leaf (-24)) (.branch 50 (.leaf (-21)) (.leaf (-18))))) (.branch 53 (.branch 52 (.leaf (-15)) (.leaf (-12))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 19 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD7_027_319 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (4)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (0)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (4)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (2))) (.branch 34 (.leaf (0)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (3)) (.branch 37 (.leaf (5)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (1))) (.branch 41 (.leaf (4)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (3)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (6))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (5)) (.leaf (3)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_319
  counts := ![(.branch 26 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 42 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 38 (.leaf (10)) (.leaf (11)))) (.branch 49 (.branch 46 (.leaf (12)) (.leaf (13))) (.branch 53 (.leaf (14)) (.leaf (15)))))),
  (.branch 25 (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 48 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 33 (.leaf (5)) (.branch 39 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 29 (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 43 (.branch 36 (.leaf (4)) (.leaf (5))) (.branch 52 (.leaf (6)) (.leaf (7))))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.branch 55 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 47 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-31)) (.leaf (-51)))),
  (.branch 21 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.branch 48 (.leaf (-5)) (.leaf (-7))))),
  (.branch 4 (.leaf (0)) (.branch 44 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (-11))) (.branch 36 (.leaf (-18)) (.branch 43 (.leaf (-22)) (.leaf (-27))))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-17))) (.branch 32 (.leaf (-22)) (.leaf (-23))))]
  high := ![(.branch 50 (.branch 4 (.leaf (-51)) (.branch 27 (.leaf (-50)) (.leaf (-49)))) (.branch 54 (.leaf (-47)) (.branch 55 (.leaf (-36)) (.leaf (-25))))),
  (.branch 49 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-5)))),
  (.branch 51 (.branch 45 (.leaf (-8)) (.leaf (-7))) (.branch 52 (.leaf (-3)) (.leaf (0)))),
  (.branch 53 (.branch 44 (.leaf (-27)) (.leaf (-26))) (.branch 54 (.leaf (-23)) (.branch 55 (.leaf (-20)) (.leaf (-17))))),
  (.leaf (-1)),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 51 (.branch 48 (.branch 33 (.leaf (-23)) (.leaf (-22))) (.branch 49 (.leaf (-20)) (.branch 50 (.leaf (-18)) (.leaf (-16))))) (.branch 53 (.branch 52 (.leaf (-14)) (.leaf (-12))) (.branch 54 (.leaf (-10)) (.branch 55 (.leaf (-8)) (.leaf (-6))))))]
def witnessD7_027_320 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (6)) (.branch 16 (.leaf (2)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 24 (.branch 22 (.leaf (2)) (.branch 23 (.leaf (4)) (.leaf (5)))) (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (3)) (.leaf (2))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (6))) (.branch 34 (.leaf (3)) (.leaf (1))))) (.branch 38 (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (2)))) (.branch 40 (.branch 39 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (3)) (.leaf (0)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (5)) (.branch 44 (.leaf (2)) (.leaf (1)))) (.branch 47 (.branch 46 (.leaf (0)) (.leaf (3))) (.branch 48 (.leaf (0)) (.leaf (1))))) (.branch 52 (.branch 50 (.leaf (2)) (.branch 51 (.leaf (4)) (.leaf (6)))) (.branch 54 (.branch 53 (.leaf (0)) (.leaf (1))) (.branch 55 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_320
  counts := ![(.branch 25 (.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))) (.branch 39 (.branch 31 (.branch 29 (.leaf (8)) (.leaf (9))) (.branch 36 (.leaf (10)) (.leaf (11)))) (.branch 46 (.branch 42 (.leaf (12)) (.leaf (13))) (.branch 48 (.leaf (14)) (.branch 53 (.leaf (15)) (.leaf (16))))))),
  (.branch 26 (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))) (.branch 40 (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))) (.branch 49 (.branch 45 (.leaf (9)) (.leaf (10))) (.branch 54 (.leaf (11)) (.leaf (12)))))),
  (.branch 28 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))) (.branch 44 (.branch 32 (.leaf (5)) (.branch 38 (.leaf (6)) (.leaf (7)))) (.branch 50 (.leaf (8)) (.branch 56 (.leaf (9)) (.leaf (10)))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 47 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.branch 51 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 43 (.leaf (2)) (.leaf (3)))),
  (.branch 33 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 52 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 20 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-5)) (.leaf (-6)))) (.branch 42 (.branch 31 (.leaf (-8)) (.leaf (-9))) (.branch 48 (.leaf (-10)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.branch 32 (.leaf (-7)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-41))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (-11)) (.leaf (-13))))]
  high := ![(.branch 54 (.branch 49 (.leaf (-12)) (.leaf (-11))) (.branch 55 (.leaf (-10)) (.leaf (-9)))),
  (.branch 50 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 45 (.branch 33 (.leaf (-10)) (.branch 39 (.leaf (-9)) (.leaf (-8)))) (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-3)) (.leaf (0))))),
  (.branch 48 (.leaf (-2)) (.leaf (-1))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.branch 48 (.branch 44 (.branch 6 (.leaf (-41)) (.branch 25 (.leaf (-40)) (.leaf (-39)))) (.branch 46 (.branch 45 (.leaf (-36)) (.leaf (-33))) (.branch 47 (.leaf (-30)) (.leaf (-27))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-24)) (.leaf (-21))) (.branch 51 (.leaf (-18)) (.leaf (-15)))) (.branch 54 (.branch 53 (.leaf (-12)) (.leaf (-9))) (.branch 55 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 53 (.branch 34 (.leaf (-13)) (.leaf (-12))) (.branch 54 (.leaf (-9)) (.branch 55 (.leaf (-6)) (.leaf (-3)))))]
def witnessD7_027_321 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (6))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (0))) (.branch 34 (.leaf (1)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (2)) (.leaf (0))) (.branch 41 (.leaf (1)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (6)) (.leaf (0))) (.branch 48 (.leaf (1)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (4)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (2)) (.leaf (0))) (.branch 55 (.leaf (1)) (.leaf (5))))))))
  code := certificateD7_321
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 27 (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))) (.branch 41 (.branch 34 (.branch 30 (.leaf (8)) (.leaf (9))) (.branch 37 (.leaf (10)) (.leaf (11)))) (.branch 48 (.branch 44 (.leaf (12)) (.leaf (13))) (.branch 51 (.leaf (14)) (.branch 55 (.leaf (15)) (.leaf (16))))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 50 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-15)) (.leaf (-16)))),
  (.branch 32 (.branch 14 (.leaf (0)) (.leaf (-5))) (.branch 50 (.leaf (-6)) (.leaf (-7)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 50 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 52 (.leaf (-3)) (.leaf (-2))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 48 (.branch 44 (.branch 23 (.leaf (-16)) (.branch 43 (.leaf (-15)) (.leaf (-14)))) (.branch 46 (.branch 45 (.leaf (-13)) (.leaf (-12))) (.branch 47 (.leaf (-11)) (.leaf (-10))))) (.branch 52 (.branch 50 (.branch 49 (.leaf (-9)) (.leaf (-8))) (.branch 51 (.leaf (-7)) (.leaf (-6)))) (.branch 54 (.branch 53 (.leaf (-5)) (.leaf (-4))) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 53 (.branch 51 (.leaf (-7)) (.branch 52 (.leaf (-6)) (.leaf (-5)))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2))))),
  (.branch 37 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0)))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_027_322 : CycleWitness 7 where
  length := 56
  word := (.branch 28 (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (6)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 24 (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (0)))) (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (5))))))) (.branch 42 (.branch 35 (.branch 31 (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (3)) (.leaf (0))) (.branch 34 (.leaf (2)) (.leaf (0))))) (.branch 38 (.branch 36 (.leaf (6)) (.branch 37 (.leaf (1)) (.leaf (0)))) (.branch 40 (.branch 39 (.leaf (4)) (.leaf (0))) (.branch 41 (.leaf (2)) (.leaf (3)))))) (.branch 49 (.branch 45 (.branch 43 (.leaf (0)) (.branch 44 (.leaf (1)) (.leaf (0)))) (.branch 47 (.branch 46 (.leaf (5)) (.leaf (0))) (.branch 48 (.leaf (2)) (.leaf (0))))) (.branch 52 (.branch 50 (.leaf (3)) (.branch 51 (.leaf (1)) (.leaf (0)))) (.branch 54 (.branch 53 (.leaf (4)) (.leaf (0))) (.branch 55 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_322
  counts := ![(.branch 26 (.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))) (.branch 21 (.leaf (9)) (.branch 24 (.leaf (10)) (.leaf (11)))))) (.branch 40 (.branch 33 (.branch 29 (.leaf (12)) (.branch 31 (.leaf (13)) (.leaf (14)))) (.branch 35 (.leaf (15)) (.branch 38 (.leaf (16)) (.leaf (17))))) (.branch 47 (.branch 43 (.leaf (18)) (.branch 45 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 49 (.leaf (21)) (.leaf (22))) (.branch 54 (.leaf (23)) (.leaf (24))))))),
  (.branch 23 (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 37 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 44 (.leaf (6)) (.branch 51 (.leaf (7)) (.leaf (8)))))),
  (.branch 27 (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 41 (.branch 34 (.leaf (4)) (.leaf (5))) (.branch 48 (.leaf (6)) (.branch 55 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 42 (.branch 32 (.leaf (3)) (.leaf (4))) (.branch 50 (.leaf (5)) (.leaf (6))))),
  (.branch 25 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.branch 53 (.leaf (3)) (.leaf (4))))),
  (.branch 28 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 46 (.leaf (2)) (.leaf (3)))),
  (.branch 36 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 56 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.branch 7 (.leaf (-6)) (.leaf (-7))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 22 (.branch 4 (.leaf (0)) (.leaf (-11))) (.branch 50 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-11))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 50 (.leaf (-7)) (.branch 55 (.leaf (-6)) (.leaf (-3)))),
  (.branch 53 (.branch 52 (.leaf (-5)) (.leaf (-4))) (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 53 (.branch 51 (.leaf (-14)) (.branch 52 (.leaf (-12)) (.leaf (-10)))) (.branch 54 (.leaf (-8)) (.branch 55 (.leaf (-6)) (.leaf (-4))))),
  (.branch 54 (.leaf (-3)) (.branch 55 (.leaf (-2)) (.leaf (-1)))),
  (.branch 51 (.branch 48 (.branch 47 (.leaf (-11)) (.leaf (-10))) (.branch 49 (.leaf (-9)) (.branch 50 (.leaf (-8)) (.leaf (-7))))) (.branch 53 (.branch 52 (.leaf (-6)) (.leaf (-5))) (.branch 54 (.leaf (-4)) (.branch 55 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 37 (.leaf (-2)) (.branch 38 (.leaf (-1)) (.leaf (0))))]
def witnessD7_027 : Fin 17 → CycleWitness 7 := ![witnessD7_027_306, witnessD7_027_307, witnessD7_027_308, witnessD7_027_309, witnessD7_027_310, witnessD7_027_311, witnessD7_027_312, witnessD7_027_313, witnessD7_027_314, witnessD7_027_315, witnessD7_027_316, witnessD7_027_317, witnessD7_027_318, witnessD7_027_319, witnessD7_027_320, witnessD7_027_321, witnessD7_027_322]
end RealPinwheel.FiveSixths


