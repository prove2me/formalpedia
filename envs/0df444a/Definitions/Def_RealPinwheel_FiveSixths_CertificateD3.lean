-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CertificateD3
-- name    : RealPinwheel_FiveSixths_CertificateD3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:11:54.599777+00:00
-- url     : https://prove2.me/theorems/3cac0498-d3ba-4ff3-a415-cebfa157b597
-- title:
--   Three-task five-sixths certificate words
-- statement:
--   The array contains the eighteen three-task words and their rational density-box annotations in the source's certificate family $W_3$. Its greatest word length is twelve.
--
--   $$|W_3|=18,\qquad\max_{w\in W_3}|w|=12.$$
--
--   The data carries no schedulability or coverage assumption. Those assertions require separate verification.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 3, dominance boxes and equation (2), printed pp. 7–8 (PDF pp. 8–9), Section 4 Table 1, printed p. 10 (PDF p. 11). Exact data: https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D3.txt

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

def certificateD3 : Array CycleCode := #[
{ word := "AAAAABAAAAAC", num := #[5, 1, 1], den := #[6, 12, 12], strict := #[false, false, false] },
{ word := "AAABAACAAB", num := #[7, 1, 1], den := #[10, 5, 10], strict := #[false, true, false] },
{ word := "AABAABACAB", num := #[3, 3, 1], den := #[5, 10, 10], strict := #[true, false, false] },
{ word := "AABABACBAB", num := #[1, 2, 1], den := #[2, 5, 10], strict := #[true, false, false] },
{ word := "AAABAACAB", num := #[2, 2, 1], den := #[3, 9, 9], strict := #[true, false, false] },
{ word := "AABABACAB", num := #[5, 1, 1], den := #[9, 3, 9], strict := #[false, true, false] },
{ word := "ABABABABC", num := #[4, 4, 1], den := #[9, 9, 9], strict := #[false, false, false] },
{ word := "AAABAAAC", num := #[3, 1, 1], den := #[4, 8, 8], strict := #[false, false, false] },
{ word := "AABAABAC", num := #[5, 1, 1], den := #[8, 4, 8], strict := #[false, true, false] },
{ word := "ABACBABC", num := #[3, 3, 1], den := #[8, 8, 4], strict := #[false, false, false] },
{ word := "AAABAAC", num := #[5, 1, 1], den := #[7, 7, 7], strict := #[false, false, false] },
{ word := "AABACAB", num := #[4, 2, 1], den := #[7, 7, 7], strict := #[false, false, false] },
{ word := "ABACABC", num := #[3, 2, 2], den := #[7, 7, 7], strict := #[false, false, false] },
{ word := "AABACB", num := #[1, 1, 1], den := #[2, 3, 6], strict := #[true, false, false] },
{ word := "AABAC", num := #[3, 1, 1], den := #[5, 5, 5], strict := #[false, false, false] },
{ word := "ABABC", num := #[2, 2, 1], den := #[5, 5, 5], strict := #[false, false, false] },
{ word := "ABAC", num := #[1, 1, 1], den := #[2, 4, 4], strict := #[false, false, false] },
{ word := "ABC", num := #[1, 1, 1], den := #[3, 3, 3], strict := #[false, false, false] }
]

end RealPinwheel.FiveSixths


