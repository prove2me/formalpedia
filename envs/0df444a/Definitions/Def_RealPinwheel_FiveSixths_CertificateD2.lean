-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CertificateD2
-- name    : RealPinwheel_FiveSixths_CertificateD2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:18:20.401793+00:00
-- url     : https://prove2.me/theorems/e2fc8915-16d8-4654-9154-8a98a8299e03
-- title:
--   Five-sixths certificate family D2
-- statement:
--   The array stores the 3 explicit words and rational box annotations in certificate family $W_2$. The source's Table 1 gives maximum word length 6.
--
--   $$|W_2|=3,\qquad\max_w|w|=6.$$
--
--   These are finite data. Validity of the encoded boxes and coverage of the real density domain require separate proofs.
-- source:
--   Fujiwara et al., STOC 2027 submission #885, Section 4 Table 1, printed p. 10 (PDF p. 11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; exact data https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D2.txt

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

def certificateD2 : Array CycleCode := #[
{ word := "AAAAAB", num := #[5, 1], den := #[6, 6], strict := #[false, false] },
{ word := "AAB", num := #[2, 1], den := #[3, 3], strict := #[false, false] },
{ word := "AB", num := #[1, 1], den := #[2, 2], strict := #[false, false] }
]

end RealPinwheel.FiveSixths


