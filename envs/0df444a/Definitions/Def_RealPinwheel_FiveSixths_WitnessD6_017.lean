-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_017
-- name    : RealPinwheel_FiveSixths_WitnessD6_017
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:33:08.935644+00:00
-- url     : https://prove2.me/theorems/acff45ae-5713-4c6a-8ea2-8aff43e94f61
-- title:
--   Exact witness block D6_017
-- statement:
--   These exact witnesses represent words 595 through 630 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 595–630; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_017_594 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (2))))))
  code := certificateD6_594
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-6)) (.leaf (-5))) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_017_595 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2))))))
  code := certificateD6_595
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 9 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-2)) (.branch 10 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_017_596 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (4))))))
  code := certificateD6_596
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.branch 9 (.leaf (-4)) (.leaf (-3)))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_017_597 : CycleWitness 6 where
  length := 13
  word := (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_597
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-11)) (.leaf (-8))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 6 (.leaf (-8)) (.branch 7 (.leaf (-7)) (.leaf (-6))))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_598 : CycleWitness 6 where
  length := 13
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 11 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_598
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))),
  (.branch 12 (.leaf (-4)) (.leaf (-2))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 6 (.leaf (-8)) (.branch 7 (.leaf (-7)) (.leaf (-6))))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_017_599 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_599
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 7 (.leaf (-9)) (.branch 9 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-11)) (.leaf (-6))),
  (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_600 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_600
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 6 (.leaf (-9)) (.leaf (-6))),
  (.branch 10 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 5 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.branch 7 (.leaf (-7)) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_017_601 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (5))))))
  code := certificateD6_601
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-11)) (.branch 12 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_602 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_602
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 9 (.leaf (-12)) (.branch 12 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-6)) (.leaf (-4))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_017_603 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_603
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-11)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 9 (.leaf (-7)) (.leaf (-4))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.leaf (-7)) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_604 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_604
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 2 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-5)))),
  (.branch 7 (.leaf (-8)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_605 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_605
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 7 (.leaf (-8)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (0)))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_017_606 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (2)) (.leaf (5))))))
  code := certificateD6_606
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-9))) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-5)) (.leaf (-3))),
  (.branch 5 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_607 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (5))))))
  code := certificateD6_607
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 5 (.leaf (-10)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_608 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (4))))))
  code := certificateD6_608
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-9))) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-5)) (.leaf (-3))),
  (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_017_609 : CycleWitness 6 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (2))))))
  code := certificateD6_609
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 8 (.leaf (-11)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_017_610 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2))))))
  code := certificateD6_610
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 3 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-7)))),
  (.branch 7 (.branch 5 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 6 (.leaf (-7)) (.leaf (-6)))) (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 6 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_017_611 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_611
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-10)) (.leaf (-5))),
  (.branch 3 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.branch 6 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD6_017_612 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4))))))
  code := certificateD6_612
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 7 (.branch 5 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 6 (.leaf (-7)) (.leaf (-6)))) (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 9 (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_017_613 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_613
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.branch 6 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_614 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (4))))))
  code := certificateD6_614
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_017_615 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (0)) (.leaf (2))))))
  code := certificateD6_615
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 2 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.branch 5 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 6 (.leaf (-7)) (.leaf (-6)))) (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_017_616 : CycleWitness 6 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_616
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_617 : CycleWitness 6 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_617
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 6 (.leaf (-8)) (.leaf (-5))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.branch 7 (.leaf (-5)) (.leaf (-4))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-2)) (.leaf (-1))),
  (.branch 7 (.branch 5 (.leaf (-7)) (.branch 6 (.leaf (-6)) (.leaf (-5)))) (.branch 9 (.branch 8 (.leaf (-4)) (.leaf (-3))) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_618 : CycleWitness 6 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (2)) (.leaf (5))))))
  code := certificateD6_618
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 4 (.leaf (-5)) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.branch 7 (.leaf (-5)) (.leaf (-4))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_017_619 : CycleWitness 6 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (5)) (.leaf (3))))))
  code := certificateD6_619
  counts := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-8))) (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-4)) (.leaf (-2))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1))]
def witnessD6_017_620 : CycleWitness 6 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_620
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 6 (.branch 4 (.leaf (-7)) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_017_621 : CycleWitness 6 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_621
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-6)) (.leaf (-3)))),
  (.branch 3 (.leaf (-4)) (.leaf (-3))),
  (.branch 7 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 6 (.branch 4 (.leaf (-7)) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_017_622 : CycleWitness 6 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_622
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 2 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 6 (.branch 4 (.leaf (-7)) (.branch 5 (.leaf (-6)) (.leaf (-5)))) (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_017_623 : CycleWitness 6 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_623
  counts := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.branch 5 (.leaf (-6)) (.branch 6 (.leaf (-5)) (.leaf (-4)))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_017_624 : CycleWitness 6 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_624
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 2 (.leaf (-5)) (.leaf (-4))),
  (.branch 5 (.branch 3 (.leaf (-7)) (.branch 4 (.leaf (-6)) (.leaf (-5)))) (.branch 7 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.branch 4 (.leaf (-6)) (.branch 5 (.leaf (-5)) (.leaf (-4)))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 7 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 8 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_017_625 : CycleWitness 6 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (3))))))
  code := certificateD6_625
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 8 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 6 (.branch 4 (.leaf (-6)) (.branch 5 (.leaf (-5)) (.leaf (-4)))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_017_626 : CycleWitness 6 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_626
  counts := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-6))) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 3 (.leaf (-5)) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.branch 4 (.leaf (-6)) (.branch 5 (.leaf (-5)) (.leaf (-4)))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_017_627 : CycleWitness 6 where
  length := 8
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1)))))
  code := certificateD6_627
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 7 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.branch 3 (.leaf (-6)) (.branch 4 (.leaf (-5)) (.leaf (-4)))) (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 5 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_017_628 : CycleWitness 6 where
  length := 8
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (2)))))
  code := certificateD6_628
  counts := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 5 (.branch 3 (.leaf (-6)) (.branch 4 (.leaf (-5)) (.leaf (-4)))) (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_017_629 : CycleWitness 6 where
  length := 6
  word := (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (3)))))
  code := certificateD6_629
  counts := ![(.branch 1 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 3 (.branch 2 (.leaf (-5)) (.leaf (-4))) (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-2)) (.leaf (-1))))),
  (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-2)) (.leaf (-1)))),
  (.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.branch 3 (.leaf (-4)) (.leaf (-3))) (.branch 5 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessD6_017 : Fin 36 → CycleWitness 6 := ![witnessD6_017_594, witnessD6_017_595, witnessD6_017_596, witnessD6_017_597, witnessD6_017_598, witnessD6_017_599, witnessD6_017_600, witnessD6_017_601, witnessD6_017_602, witnessD6_017_603, witnessD6_017_604, witnessD6_017_605, witnessD6_017_606, witnessD6_017_607, witnessD6_017_608, witnessD6_017_609, witnessD6_017_610, witnessD6_017_611, witnessD6_017_612, witnessD6_017_613, witnessD6_017_614, witnessD6_017_615, witnessD6_017_616, witnessD6_017_617, witnessD6_017_618, witnessD6_017_619, witnessD6_017_620, witnessD6_017_621, witnessD6_017_622, witnessD6_017_623, witnessD6_017_624, witnessD6_017_625, witnessD6_017_626, witnessD6_017_627, witnessD6_017_628, witnessD6_017_629]
end RealPinwheel.FiveSixths


