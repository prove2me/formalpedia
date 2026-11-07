-- Prove2me | Definitions.Def_KarpLiptonOM_OUM
-- name    : KarpLiptonOM_OUM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:45.639313+00:00
-- url     : https://prove2.me/theorems/a7a1b5fb-e8ce-4359-a06a-4c09ad5d6c8d
-- title:
--   $\mathrm{OUM} = \mathrm{OUGTD}[\mathrm{FP}^{\mathrm{sOprMA}}, \text{co-ONP}, \mathrm P]$
-- statement:
--   The class
--   $$
--   \mathrm{OUM} = \mathrm{OUGTD}[\mathrm{FP}^{\mathrm{sOprMA}}, \text{co-ONP}, \mathrm P]
--   $$
--   is the subclass of OM in which the co-ONP tester accepts exactly one advice string of each length.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.4, p.24 (and p.5)

import Mathlib
import Definitions.Def_KarpLiptonOM_OUGTD
import Definitions.Def_KarpLiptonOM_sOprMA
import Definitions.Def_KarpLiptonOM_coONP2

namespace KarpLiptonOM

/-- The unique-advice subclass `OUM = OUGTD[FP^sOprMA, co-ONP, P]` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.4, p.24; p.5). -/
def OUM : Set (Set (List Bool)) := OUGTD {PP | sOprMA PP} {T | coONP2 T}

end KarpLiptonOM


