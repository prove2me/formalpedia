-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CertificateD1
-- name    : RealPinwheel_FiveSixths_CertificateD1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:18:24.627201+00:00
-- url     : https://prove2.me/theorems/7f2b0034-9854-4a79-b5c3-be85f7e1cae0
-- title:
--   Five-sixths certificate family D1
-- statement:
--   The array stores the 1 explicit words and rational box annotations in certificate family $W_1$. The source's Table 1 gives maximum word length 1.
--
--   $$|W_1|=1,\qquad\max_w|w|=1.$$
--
--   These are finite data. Validity of the encoded boxes and coverage of the real density domain require separate proofs.
-- source:
--   Fujiwara et al., STOC 2027 submission #885, Section 4 Table 1, printed p. 10 (PDF p. 11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; exact data https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D1.txt

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

def certificateD1 : Array CycleCode := #[
{ word := "A", num := #[1], den := #[1], strict := #[false] }
]

end RealPinwheel.FiveSixths


