-- Prove2me | Definitions.Def_KarpLiptonOM_OM
-- name    : KarpLiptonOM_OM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:49.903075+00:00
-- url     : https://prove2.me/theorems/0ffe6e7c-06e4-4b94-90b9-851dc3add689
-- title:
--   $\mathrm{OM} = \mathrm{OGTD}[\mathrm{FP}^{\mathrm{sOprMA}}, \text{co-ONP}, \mathrm P]$
-- statement:
--   The class
--   $$
--   \mathrm{OM} = \mathrm{OGTD}[\mathrm{FP}^{\mathrm{sOprMA}}, \text{co-ONP}, \mathrm P]
--   $$
--   consists of the languages decided by a polynomial-time generator with an sOprMA oracle that computes advice from $1^n$, a co-ONP tester that accepts every legal output of the generator and only good advice, and a polynomial-time decoder. The name is the common prefix of OMA and OMIN.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.4, p.24 (and p.5)

import Mathlib
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_sOprMA
import Definitions.Def_KarpLiptonOM_coONP2

namespace KarpLiptonOM

/-- The main class `OM = OGTD[FP^sOprMA, co-ONP, P]` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.4, p.24; p.5): generators with an
sOprMA oracle, testers in co-ONP, decoders in P. -/
def OM : Set (Set (List Bool)) := OGTD {PP | sOprMA PP} {T | coONP2 T}

end KarpLiptonOM


