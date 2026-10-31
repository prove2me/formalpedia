-- Prove2me | Definitions.Def_OAIQ107D132
-- name    : OAIQ107D132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:14:34.068725+00:00
-- url     : https://prove2.me/theorems/f73c8d76-d885-4b9e-aaa9-25979b644ff8
-- title:
--   Definitions bundle OAIQ107D132 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 568 declarations of OpenAI's Lean: 568 definitions. The definitions and types are `OAI.CycleClique.certificate_2789`, `OAI.CycleClique.certificate_2789_part_1`, `OAI.CycleClique.certificate_2789_part_2`, `OAI.CycleClique.certificate_2789_part_3`, `OAI.CycleClique.certificate_2789_part_4`, `OAI.CycleClique.certificate_279`, `OAI.CycleClique.certificate_28`, `OAI.CycleClique.certificate_2813`, `OAI.CycleClique.certificate_2813_part_3`, `OAI.CycleClique.certificate_2813_part_4`, `OAI.CycleClique.certificate_2817`, `OAI.CycleClique.certificate_2817_part_1`, `OAI.CycleClique.certificate_2817_part_2`, `OAI.CycleClique.certificate_2817_part_3`, `OAI.CycleClique.certificate_2817_part_4`, `OAI.CycleClique.certificate_2838`, `OAI.CycleClique.certificate_2839`, `OAI.CycleClique.certificate_2839_part_1`, `OAI.CycleClique.certificate_2839_part_2`, `OAI.CycleClique.certificate_2839_part_3`, `OAI.CycleClique.certificate_2839_part_4`, `OAI.CycleClique.certificate_284`, `OAI.CycleClique.certificate_284_part_1`, `OAI.CycleClique.certificate_284_part_10_M`, `OAI.CycleClique.certificate_284_part_11_M`, `OAI.CycleClique.certificate_284_part_12_M`, `OAI.CycleClique.certificate_284_part_13_M`, `OAI.CycleClique.certificate_284_part_14_M`, `OAI.CycleClique.certificate_284_part_15_E`, `OAI.CycleClique.certificate_284_part_15_M`, `OAI.CycleClique.certificate_284_part_16_M`, `OAI.CycleClique.certificate_284_part_17_M`, `OAI.CycleClique.certificate_284_part_18`, `OAI.CycleClique.certificate_284_part_18_M`, `OAI.CycleClique.certificate_284_part_19`, `OAI.CycleClique.certificate_284_part_19_M`, `OAI.CycleClique.certificate_284_part_1_M`, `OAI.CycleClique.certificate_284_part_2`, `OAI.CycleClique.certificate_284_part_20_M`, `OAI.CycleClique.certificate_284_part_21_M` and 528 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates002`, `Ramsey_CycleClique_Certificates009`, `Ramsey_CycleClique_Certificates012`, `Ramsey_CycleClique_Certificates013`, `Ramsey_CycleClique_Certificates016`, `Ramsey_CycleClique_Certificates017`, `Ramsey_CycleClique_Certificates018`, `Ramsey_CycleClique_Certificates088`, `Ramsey_CycleClique_Certificates089`, `Ramsey_CycleClique_Certificates090`, `Ramsey_CycleClique_Certificates091`, `Ramsey_CycleClique_Certificates092`, `Ramsey_CycleClique_Certificates093`, `Ramsey_CycleClique_Certificates094`, `Ramsey_CycleClique_Certificates095`, `Ramsey_CycleClique_Certificates096`.
--
--   **Imports.** It imports the bundles `OAIQ107D020`, `OAIQ107D039`, `OAIQ107D061`, `OAIQ107D069`, `OAIQ107D071`, `OAIQ107D072`, `OAIQ107D077`, `OAIQ107D081`, `OAIQ107D084`, `OAIQ107D086`, `OAIQ107D089`, `OAIQ107D092`, `OAIQ107D093`, `OAIQ107D094`, `OAIQ107D095`, `OAIQ107D096`, `OAIQ107D097`, `OAIQ107D098`, `OAIQ107D099`, `OAIQ107D100`, `OAIQ107D101`, `OAIQ107D102`, `OAIQ107D103`, `OAIQ107D104`, `OAIQ107D105`, `OAIQ107D106`, `OAIQ107D107`, `OAIQ107D108`, `OAIQ107D109` and `OAIQ107D110` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ107D134`; the proofs of `OAI.CycleClique.finite_patterns_11_6`, `OAI.CycleClique.finite_patterns_12_6`, `OAI.CycleClique.finite_patterns_12_7`, `OAI.CycleClique.finite_patterns_17_8`, `OAI.CycleClique.finite_patterns_7_3`, `OAI.CycleClique.finite_patterns_8_4`, `OAI.CycleClique.patterns_13_6_0_verified`, `OAI.CycleClique.patterns_17_8_37_verified`, `OAI.CycleClique.patterns_17_8_38_verified`, `OAI.CycleClique.patterns_17_8_40_verified`, `OAI.CycleClique.patterns_17_8_41_verified`, `OAI.CycleClique.patterns_17_8_43_verified`, `OAI.CycleClique.patterns_17_8_44_verified`, `OAI.CycleClique.patterns_17_8_48_verified`, `OAI.CycleClique.patterns_17_8_49_verified`, `OAI.CycleClique.patterns_17_8_51_verified`, `OAI.CycleClique.patterns_17_8_52_verified` and `OAI.CycleClique.patterns_17_8_53_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ107D020
import Definitions.Def_OAIQ107D039
import Definitions.Def_OAIQ107D061
import Definitions.Def_OAIQ107D069
import Definitions.Def_OAIQ107D071
import Definitions.Def_OAIQ107D072
import Definitions.Def_OAIQ107D077
import Definitions.Def_OAIQ107D081
import Definitions.Def_OAIQ107D084
import Definitions.Def_OAIQ107D086
import Definitions.Def_OAIQ107D089
import Definitions.Def_OAIQ107D092
import Definitions.Def_OAIQ107D093
import Definitions.Def_OAIQ107D094
import Definitions.Def_OAIQ107D095
import Definitions.Def_OAIQ107D096
import Definitions.Def_OAIQ107D097
import Definitions.Def_OAIQ107D098
import Definitions.Def_OAIQ107D099
import Definitions.Def_OAIQ107D100
import Definitions.Def_OAIQ107D101
import Definitions.Def_OAIQ107D102
import Definitions.Def_OAIQ107D103
import Definitions.Def_OAIQ107D104
import Definitions.Def_OAIQ107D105
import Definitions.Def_OAIQ107D106
import Definitions.Def_OAIQ107D107
import Definitions.Def_OAIQ107D108
import Definitions.Def_OAIQ107D109
import Definitions.Def_OAIQ107D110

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2_part_1_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,1) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (certificate_2_M))))))))))))))))

noncomputable def certificate_2_part_2_M : ForbiddenMatrix := ((0,4,2) :: (((3,4,2) :: (((3,4,1) :: (((2,4,2) :: (((0,1,1) :: (((2,3,1) :: (((0,4,4) :: (certificate_2_part_1_M))))))))))))))

noncomputable def certificate_2_part_3_M : ForbiddenMatrix := ((2,3,2) :: (((1,3,0) :: (((3,4,2) :: (((3,4,1) :: (((2,4,2) :: (((0,1,1) :: (((2,3,1) :: (((0,4,4) :: (certificate_2_part_1_M))))))))))))))))

noncomputable def certificate_2_part_4_M : ForbiddenMatrix := ((0,1,2) :: (((1,3,3) :: (((1,3,2) :: (((1,2,2) :: (((1,2,1) :: (((0,1,4) :: (((0,1,3) :: (certificate_2_part_3_M))))))))))))))

noncomputable def certificate_2_part_5_M : ForbiddenMatrix := ((2,4,0) :: (((1,3,3) :: (((1,3,2) :: (((1,2,2) :: (((1,2,1) :: (((0,1,4) :: (((0,1,3) :: (certificate_2_part_3_M))))))))))))))

noncomputable def certificate_2_part_6_M : ForbiddenMatrix := ((2,4,1) :: (((2,4,0) :: (((1,3,3) :: (((1,3,2) :: (((1,2,2) :: (((1,2,1) :: (((0,1,4) :: (((0,1,3) :: (certificate_2_part_3_M))))))))))))))))

noncomputable def certificate_3_part_1_M : ForbiddenMatrix := ((0,4,1) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_3_M))))))))))))))))

noncomputable def certificate_3 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1,2],[4]]) (.forbid 0 1 2 (.system [[0,5,6,1,2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1,2],[4]]) (.forbid 0 1 4 (.cycle [0,1,8,7,6,5]) (.forbid 0 3 1 (.system [[0,5,3,2],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,2],[4]]) (.forbid 0 4 1 (.cycle [0,1,2,3,4,5]) (certificate_3_part_1))))))))

noncomputable def certificate_28_part_1_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,1) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_28_M))))))))))))))))

noncomputable def certificate_28_part_2_M : ForbiddenMatrix := ((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,1) :: (((0,5,1) :: (((0,3,5) :: (((0,3,4) :: (certificate_28_part_1_M))))))))))))))))

noncomputable def certificate_28_part_3_M : ForbiddenMatrix := ((3,5,2) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,4,0) :: (((2,3,1) :: (((1,3,5) :: (certificate_28_part_2_M))))))))))))))))

noncomputable def certificate_28_part_4_M : ForbiddenMatrix := ((3,5,1) :: (((3,5,0) :: (((1,7,0) :: (((1,5,0) :: (((1,3,0) :: (((3,5,4) :: (((3,5,3) :: (certificate_28_part_3_M))))))))))))))

noncomputable def certificate_28_part_5_M : ForbiddenMatrix := ((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (certificate_28_part_3_M))))))))))))))

noncomputable def certificate_28_part_6_M : ForbiddenMatrix := ((1,3,0) :: (((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (certificate_28_part_3_M))))))))))))))))

noncomputable def certificate_28_part_3 : FiniteCertificate := .forbid 3 5 3 (.system [[0],[2,3,7,8,9,5,6]]) (.forbid 3 5 4 (.system [[0],[2,3,7,8,9,10,5,6]]) (.forbid 0 4 1 (.forbid 1 3 0 (.cycle [1,0,7,4,5,6,2,3]) (.forbid 1 5 0 (.cycle [1,0,7,4,3,2,6,5]) (.forbid 1 7 0 (.cycle [1,2,3,4,5,6,0,7]) (.forbid 3 5 0 (.cycle [3,4,7,0,1,2,6,5]) (.forbid 3 5 1 (.cycle [3,2,1,0,7,4,5,8]) (certificate_28_part_4)))))) (.forbid 0 4 2 (.system [[0,7,8,4,3,2],[6]]) (.forbid 0 4 3 (.system [[0,7,8,9,4,3,2],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4,3,2],[6]]) (.forbid 0 5 0 (.forbid 0 1 2 (.cycle [0,5,4,3,2,1,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})) (.forbid 1 3 0 (certificate_28_part_5) (certificate_28_part_6))))))))

noncomputable def certificate_28_part_2 : FiniteCertificate := .forbid 1 3 5 (.cycle [1,2,3,11,10,9,8,7]) (.forbid 2 3 1 (.system [[0],[2,7,3,4,5,6]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,5,6,2,1,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3} 4 2) ∅ 8 3), .ball 3 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})) (.forbid 1 5 1 (.system [[0,1,7,5,4,3,2],[6]]) (.forbid 1 5 2 (.system [[0,1,7,8,5,4,3,2],[6]]) (.forbid 1 5 3 (.system [[0,1,7,8,9,5,6],[2]]) (.forbid 1 5 4 (.system [[0,1,7,8,9,10,5,6],[2]]) (.forbid 3 5 2 (.system [[0],[2,3,7,8,5,6]]) (certificate_28_part_3))))))))

noncomputable def certificate_28_part_1 : FiniteCertificate := .forbid 0 3 4 (.system [[0,7,8,9,10,3,2],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3,2],[6]]) (.forbid 0 5 1 (.system [[0,7,5,4,3,2],[6]]) (.forbid 1 2 1 (.system [[0,1,7,2,3,4,5,6]]) (.forbid 1 3 1 (.system [[0,1,7,3,4,5,6],[2]]) (.forbid 1 3 2 (.system [[0,1,7,8,3,2],[6]]) (.forbid 1 3 3 (.system [[0,1,7,8,9,3,2],[6]]) (.forbid 1 3 4 (.system [[0,1,7,8,9,10,3,2],[6]]) (certificate_28_part_2))))))))

noncomputable def certificate_28 : FiniteCertificate := .forbid 0 3 1 (.system [[0,7,3,4,5,6],[2]]) (.forbid 0 3 2 (.system [[0,7,8,3,4,5,6],[2]]) (.forbid 0 3 3 (.system [[0,7,8,9,3,2],[6]]) (.forbid 0 1 1 (.system [[0,7,1,2,3,4,5,6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1,2],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1,2],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1,2],[6]]) (.forbid 0 1 6 (.cycle [0,1,12,11,10,9,8,7]) (certificate_28_part_1))))))))

noncomputable def certificate_29_part_1_M : ForbiddenMatrix := ((0,6,3) :: (((0,6,1) :: (((0,4,1) :: (((0,1,6) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_29_M))))))))))))))))

noncomputable def certificate_29_part_2_M : ForbiddenMatrix := ((2,6,1) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((1,2,1) :: (((0,6,5) :: (((0,6,4) :: (certificate_29_part_1_M))))))))))))))))

noncomputable def certificate_29_part_3_M : ForbiddenMatrix := ((1,5,2) :: (((1,5,1) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,2,2) :: (((0,2,0) :: (certificate_29_part_2_M))))))))))))))))

noncomputable def certificate_29_part_4_M : ForbiddenMatrix := ((4,5,2) :: (((4,5,1) :: (((2,5,2) :: (((2,5,1) :: (((2,4,2) :: (((2,4,1) :: (((1,5,4) :: (((1,5,3) :: (certificate_29_part_3_M))))))))))))))))

noncomputable def certificate_29_part_5_M : ForbiddenMatrix := ((1,2,3) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((5,6,1) :: (((4,5,4) :: (((4,5,3) :: (certificate_29_part_4_M))))))))))))))))

noncomputable def certificate_29_part_6_M : ForbiddenMatrix := ((0,1,5) :: (((2,3,1) :: (((0,2,5) :: (((0,4,0) :: (((2,4,5) :: (((2,4,3) :: (((1,2,4) :: (certificate_29_part_5_M))))))))))))))

noncomputable def certificate_29_part_7_M : ForbiddenMatrix := ((0,3,3) :: (((1,3,0) :: (((2,3,1) :: (((0,2,5) :: (((0,4,0) :: (((2,4,5) :: (((2,4,3) :: (((1,2,4) :: (certificate_29_part_5_M))))))))))))))))

noncomputable def certificate_29_part_8_M : ForbiddenMatrix := ((2,3,3) :: (((2,3,2) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_29_part_7_M))))))))))))))))

noncomputable def certificate_29_part_9_M : ForbiddenMatrix := ((3,6,4) :: (((3,6,3) :: (((0,6,6) :: (((1,4,0) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (certificate_29_part_8_M))))))))))))))))

noncomputable def certificate_29_part_10_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,1) :: (((0,6,2) :: (((0,3,2) :: (((0,3,1) :: (((3,6,6) :: (((3,6,5) :: (certificate_29_part_9_M))))))))))))))

noncomputable def certificate_29_part_9 : FiniteCertificate := .forbid 3 6 5 (.system [[0],[3,7,8,9,10,11,6]]) (.forbid 3 6 6 (.system [[0],[3,7,8,9,10,11,12,6]]) (.forbid 2 4 0 (.forbid 0 3 1 (.cycle [0,1,2,4,5,6,3,7]) (.forbid 0 3 2 (.cycle [0,6,5,4,2,3,8,7]) (.forbid 0 6 2 (.cycle [0,1,2,4,3,6,8,7]) (.forbid 1 3 1 (.cycle [1,0,6,5,4,2,3,7]) (.forbid 1 6 1 (.cycle [1,0,3,2,4,5,6,7]) (certificate_29_part_10)))))) (.packing {.ball 0 (.succ (.zero {2,4} 3 2) ∅ 8 3), .ball 1 (.succ (.zero {3,4} 3 2) ∅ 8 3), .ball 2 (.succ (.zero {0,4} 3 2) ∅ 8 3)})))

noncomputable def certificate_29_part_8 : FiniteCertificate := .forbid 3 4 1 (.system [[0,1,2,3,7,4,5,6]]) (.forbid 3 4 2 (.system [[0],[3,7,8,4,5,6]]) (.forbid 3 4 3 (.system [[0],[3,7,8,9,4,5,6]]) (.forbid 3 4 4 (.system [[0],[3,7,8,9,10,4,5,6]]) (.forbid 1 4 0 (.forbid 0 3 1 (.cycle [0,6,5,4,1,2,3,7]) (.forbid 0 3 2 (.cycle [0,1,4,5,6,3,8,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {2,3,4} 4 2) ∅ 8 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,2,4} 4 2) ∅ 8 3), .singleton 2, .ball 4 (.zero ∅ 1 1)}))) (.forbid 0 6 6 (.system [[0,7,8,9,10,11,12,6],[3]]) (.forbid 3 6 3 (.system [[0,1,2,3,7,8,9,6]]) (.forbid 3 6 4 (.system [[0],[3,7,8,9,10,6]]) (certificate_29_part_9))))))))

noncomputable def certificate_29_part_7 : FiniteCertificate := .forbid 0 3 4 (.system [[0,7,8,9,10,3],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3],[6]]) (.forbid 0 3 6 (.system [[0,7,8,9,10,11,12,3],[6]]) (.forbid 0 4 2 (.system [[0,7,8,4,5,6],[3]]) (.forbid 0 4 3 (.system [[0,7,8,9,4,3],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4,3],[6]]) (.forbid 2 3 2 (.system [[0,1,2,7,8,3],[6]]) (.forbid 2 3 3 (.system [[0,1,2,7,8,9,3],[6]]) (certificate_29_part_8))))))))

noncomputable def certificate_29_part_5 : FiniteCertificate := .forbid 1 2 4 (.system [[0,1,7,8,9,10,2,3],[6]]) (.forbid 2 4 3 (.system [[0,1,2,7,8,9,4,3],[6]]) (.forbid 2 4 5 (.cycle [2,3,4,11,10,9,8,7]) (.forbid 0 4 0 (.forbid 1 4 5 (.cycle [1,0,4,11,10,9,8,7]) (.forbid 2 4 4 (.cycle [2,1,0,4,10,9,8,7]) (.packing {.ball 1 (.succ (.zero ∅ 1 1) {2,4,5} 4 2), .ball 4 (.succ (.succ (.zero ∅ 1 1) {1,2,5} 4 2) ∅ 8 3), .ball 2 (.succ (.zero ∅ 1 1) {1,4,5} 4 2), .singleton 5}))) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2,3],[6]]) (.forbid 2 3 1 (.system [[0,1,2,7,3,4,5,6]]) (.forbid 1 3 0 (.forbid 0 1 5 (.cycle [0,3,1,11,10,9,8,7]) (certificate_29_part_6)) (.forbid 0 3 3 (.system [[0,7,8,9,3,4,5,6]]) (certificate_29_part_7))))))))

noncomputable def certificate_29_part_4 : FiniteCertificate := .forbid 4 5 3 (.system [[0],[3,4,7,8,9,5,6]]) (.forbid 4 5 4 (.system [[0],[3,4,7,8,9,10,5,6]]) (.forbid 5 6 1 (.system [[0,1,2,3,4,5,7,6]]) (.forbid 0 2 1 (.forbid 1 3 0 (.cycle [1,2,7,0,6,5,4,3]) (.forbid 1 4 0 (.cycle [1,0,7,2,3,6,5,4]) (.forbid 1 5 0 (.cycle [1,2,7,0,6,3,4,5]) (.packing {.ball 1 (.succ (.zero {3,4,5} 3 2) {2} 8 3), .ball 4 (.succ (.zero {1} 1 1) {0,1,2,5} 4 2), .ball 5 (.succ (.zero {1} 1 1) {1,2,4,6} 4 2), .singleton 2})))) (.forbid 0 2 2 (.system [[0,7,8,2,3,4,5,6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2,3],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2,3],[6]]) (.forbid 1 2 3 (.system [[0,1,7,8,9,2,3],[6]]) (certificate_29_part_5))))))))

noncomputable def certificate_29_part_3 : FiniteCertificate := .forbid 1 5 3 (.system [[0,1,7,8,9,5,4,3],[6]]) (.forbid 1 5 4 (.system [[0,1,7,8,9,10,5,6],[3]]) (.forbid 2 4 1 (.system [[0,1,2,7,4,3],[6]]) (.forbid 2 4 2 (.system [[0,1,2,7,8,4,3],[6]]) (.forbid 2 5 1 (.system [[0,1,2,7,5,4,3],[6]]) (.forbid 2 5 2 (.system [[0,1,2,7,8,5,4,3],[6]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,7,5,6]]) (.forbid 4 5 2 (.system [[0],[3,4,7,8,5,6]]) (certificate_29_part_4))))))))

noncomputable def certificate_29_part_2 : FiniteCertificate := .forbid 0 2 0 (.forbid 0 1 5 (.cycle [0,2,1,11,10,9,8,7]) (.forbid 0 6 2 (.cycle [0,2,3,4,5,6,8,7]) (.forbid 1 6 1 (.cycle [1,0,2,3,4,5,6,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,4,6} 4 2) ∅ 8 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,6} 4 2) ∅ 8 3), .ball 6 (.succ (.zero ∅ 1 1) {0,1,2} 4 2)})))) (.forbid 1 2 2 (.system [[0,1,7,8,2,3],[6]]) (.forbid 1 4 1 (.system [[0,1,7,4,5,6],[3]]) (.forbid 1 4 2 (.system [[0,1,7,8,4,3],[6]]) (.forbid 1 4 3 (.system [[0,1,7,8,9,4,3],[6]]) (.forbid 1 4 4 (.system [[0,1,7,8,9,10,4,3],[6]]) (.forbid 1 5 1 (.system [[0,1,7,5,4,3],[6]]) (.forbid 1 5 2 (.system [[0,1,7,8,5,4,3],[6]]) (certificate_29_part_3))))))))

noncomputable def certificate_29_part_1 : FiniteCertificate := .forbid 0 6 4 (.system [[0,7,8,9,10,6],[3]]) (.forbid 0 6 5 (.system [[0,7,8,9,10,11,6],[3]]) (.forbid 1 2 1 (.system [[0,1,7,2,3,4,5,6]]) (.forbid 1 6 2 (.system [[0,1,7,8,6,5,4,3]]) (.forbid 1 6 3 (.system [[0,1,7,8,9,6],[3]]) (.forbid 1 6 4 (.system [[0,1,7,8,9,10,6],[3]]) (.forbid 1 6 5 (.system [[0,1,7,8,9,10,11,6],[3]]) (.forbid 2 6 1 (.system [[0,1,2,7,6,5,4,3]]) (certificate_29_part_2))))))))

noncomputable def certificate_29 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1,2,3,4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1,2,3],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1,2,3],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1,2,3],[6]]) (.forbid 0 1 6 (.cycle [0,1,12,11,10,9,8,7]) (.forbid 0 4 1 (.system [[3,2,1,0,7,4,5,6]]) (.forbid 0 6 1 (.cycle [0,1,2,3,4,5,6,7]) (.forbid 0 6 3 (.system [[3,2,1,0,7,8,9,6]]) (certificate_29_part_1))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_32 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[2,3,4,5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[2],[5]]) (.forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[2],[5]]) (.forbid 0 1 6 (.system [[0,6,7,8,9,10,11,1],[2],[5]]) (.forbid 0 2 1 (.system [[0,6,2,3,4,5],[1]]) (.forbid 0 2 2 (.system [[0,6,7,2,3,4,5],[1]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[5]]) (.forbid 0 2 5 (.system [[0,6,7,8,9,10,2],[1],[5]]) (.forbid 0 2 6 (.system [[0,6,7,8,9,10,11,2],[1],[5]]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[1],[2]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3,4,5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2,3,4,5]]) (.forbid 1 2 3 (.system [[0],[1,6,7,8,2],[5]]) (.forbid 1 2 4 (.system [[0],[1,6,7,8,9,2],[5]]) (.forbid 1 2 5 (.system [[0],[1,6,7,8,9,10,2],[5]]) (.forbid 1 2 6 (.system [[0],[1,6,7,8,9,10,11,2],[5]]) (.forbid 1 3 1 (.system [[0],[1,6,3,4,5],[2]]) (certificate_32_part_0))))))))))))))))))))

noncomputable def certificate_33_part_1_M : ForbiddenMatrix := ((0,6,2) :: (((0,6,1) :: (((0,3,1) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,1,1) :: (certificate_33_M))))))))))))))))

noncomputable def certificate_33_part_2_M : ForbiddenMatrix := ((1,6,4) :: (((1,6,2) :: (((1,6,1) :: (((1,3,1) :: (((1,2,1) :: (((0,6,6) :: (((0,6,5) :: (((0,6,4) :: (certificate_33_part_1_M))))))))))))))))

noncomputable def certificate_33_part_3_M : ForbiddenMatrix := ((1,6,3) :: (((0,6,3) :: (((0,1,3) :: (((0,1,2) :: (((5,6,1) :: (((1,6,6) :: (((1,6,5) :: (certificate_33_part_2_M))))))))))))))

noncomputable def certificate_33_part_4_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,2) :: (((0,3,3) :: (((0,3,2) :: (((0,3,0) :: (((5,6,1) :: (((1,6,6) :: (((1,6,5) :: (certificate_33_part_2_M))))))))))))))))

noncomputable def certificate_33_part_5_M : ForbiddenMatrix := ((1,5,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((1,2,2) :: (((0,5,1) :: (((0,2,6) :: (((0,2,5) :: (certificate_33_part_4_M))))))))))))))))

noncomputable def certificate_33_part_6_M : ForbiddenMatrix := ((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,3,5) :: (((0,3,4) :: (((0,4,0) :: (((2,3,1) :: (certificate_33_part_5_M))))))))))))))))

noncomputable def certificate_33_part_7_M : ForbiddenMatrix := ((2,5,0) :: (((1,5,0) :: (((1,3,0) :: (((0,5,0) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_33_part_6_M))))))))))))))

noncomputable def certificate_33_part_8_M : ForbiddenMatrix := ((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_33_part_6_M))))))))))))))

noncomputable def certificate_33_part_9_M : ForbiddenMatrix := ((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_33_part_6_M))))))))))))))))

noncomputable def certificate_33_part_10_M : ForbiddenMatrix := ((4,5,1) :: (((3,5,5) :: (((1,5,2) :: (((1,3,3) :: (((1,3,2) :: (((1,4,0) :: (((1,3,0) :: (certificate_33_part_9_M))))))))))))))

noncomputable def certificate_33_part_11_M : ForbiddenMatrix := ((2,4,0) :: (((4,5,1) :: (((3,5,5) :: (((1,5,2) :: (((1,3,3) :: (((1,3,2) :: (((1,4,0) :: (((1,3,0) :: (certificate_33_part_9_M))))))))))))))))

noncomputable def certificate_33_part_12_M : ForbiddenMatrix := ((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,3,3) :: (((2,3,2) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (certificate_33_part_11_M))))))))))))))))

noncomputable def certificate_33_part_11 : FiniteCertificate := .forbid 3 4 1 (.system [[0],[1],[2,3,7,4,5,6]]) (.forbid 3 4 2 (.system [[0],[1],[2,3,7,8,4,5,6]]) (.forbid 3 4 3 (.system [[0],[1],[2,3,7,8,9,4,5,6]]) (.forbid 2 3 2 (.system [[0],[1],[2,7,8,3,4,5,6]]) (.forbid 2 3 3 (.system [[0],[1],[2,7,8,9,3,4,5,6]]) (.forbid 2 4 2 (.system [[0],[1],[2,7,8,4,5,6]]) (.forbid 2 4 3 (.system [[0],[1],[2,7,8,9,4,5,6]]) (.forbid 2 4 4 (.system [[0],[1],[2,7,8,9,10,4,5,6]]) (certificate_33_part_12))))))))

noncomputable def certificate_33_part_9 : FiniteCertificate := .forbid 1 3 0 (.forbid 0 1 2 (.cycle [0,6,5,4,3,1,8,7]) (.forbid 0 1 3 (.cycle [0,6,2,3,1,9,8,7]) (.forbid 0 6 3 (.cycle [0,1,3,2,6,9,8,7]) (.forbid 1 6 3 (.cycle [1,3,2,0,6,9,8,7]) (.forbid 2 6 1 (.cycle [2,0,1,3,4,5,6,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,6} 5 2) {1} 9 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,6} 5 2) {0} 9 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,5} 5 2) {0} 9 3)})))))) (.forbid 1 4 0 (.forbid 0 1 2 (.cycle [0,2,6,5,4,1,8,7]) (.forbid 0 1 3 (.cycle [0,2,3,4,1,9,8,7]) (.forbid 0 2 3 (.cycle [0,1,4,3,2,9,8,7]) (.forbid 1 2 3 (.cycle [1,4,5,6,2,9,8,7]) (.forbid 2 5 1 (.cycle [2,3,4,1,0,6,5,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,5} 5 2) {1} 9 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,5} 5 2) {0} 9 3), .ball 2 (.succ (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2) {0} 9 3)})))))) (.forbid 1 3 2 (.system [[0],[1,7,8,3,4,5,6],[2]]) (.forbid 1 3 3 (.system [[0],[1,7,8,9,3,2],[6]]) (.forbid 1 5 2 (.system [[0],[1,7,8,5,4,3,2],[6]]) (.forbid 3 5 5 (.cycle [3,4,5,11,10,9,8,7]) (.forbid 4 5 1 (.system [[0],[1],[2,3,4,7,5,6]]) (.forbid 2 4 0 (certificate_33_part_10) (certificate_33_part_11))))))))

noncomputable def certificate_33_part_6 : FiniteCertificate := .forbid 3 5 2 (.system [[0],[1],[2,3,7,8,5,6]]) (.forbid 3 5 3 (.system [[0],[1],[2,3,7,8,9,5,6]]) (.forbid 3 5 4 (.system [[0],[1],[2,3,7,8,9,10,5,6]]) (.forbid 0 4 1 (.forbid 0 5 0 (.cycle [0,7,4,3,2,1,6,5]) (.forbid 1 3 0 (.cycle [1,0,7,4,5,6,2,3]) (.forbid 1 5 0 (.cycle [1,0,7,4,3,2,6,5]) (.forbid 2 5 0 (.cycle [2,3,4,7,0,1,6,5]) (certificate_33_part_7))))) (.forbid 0 4 2 (.system [[0,7,8,4,3,2],[1],[6]]) (.forbid 0 4 3 (.system [[0,7,8,9,4,3,2],[1],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4,3,2],[1],[6]]) (.forbid 0 5 0 (certificate_33_part_8) (certificate_33_part_9))))))))

noncomputable def certificate_33_part_5 : FiniteCertificate := .forbid 2 3 1 (.system [[0],[1],[2,7,3,4,5,6]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,3,2,6,1,8,7]) (.forbid 0 1 3 (.cycle [0,4,3,2,1,9,8,7]) (.forbid 0 2 3 (.cycle [0,4,5,6,2,9,8,7]) (.forbid 1 2 3 (.cycle [1,0,4,3,2,9,8,7]) (.forbid 2 5 1 (.cycle [2,3,4,0,1,6,5,7]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,5} 5 2) {1} 9 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,5} 5 2) {0} 9 3), .ball 2 (.succ (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2) {0} 9 3)})))))) (.forbid 0 3 4 (.system [[0,7,8,9,10,3,2],[1],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3,2],[1],[6]]) (.forbid 0 5 2 (.system [[0,7,8,5,4,3,2],[1],[6]]) (.forbid 0 5 3 (.system [[0,7,8,9,5,4,3,2],[1],[6]]) (.forbid 0 5 4 (.system [[0,7,8,9,10,5,6],[1],[2]]) (.forbid 0 5 5 (.system [[0,7,8,9,10,11,5,6],[1],[2]]) (certificate_33_part_6))))))))

noncomputable def certificate_33_part_4 : FiniteCertificate := .forbid 0 2 5 (.system [[0,7,8,9,10,11,2],[1],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2],[1],[6]]) (.forbid 0 5 1 (.system [[0,7,5,4,3,2],[1],[6]]) (.forbid 1 2 2 (.system [[0],[1,7,8,2,3,4,5,6]]) (.forbid 1 2 4 (.system [[0],[1,7,8,9,10,2],[6]]) (.forbid 1 2 5 (.system [[0],[1,7,8,9,10,11,2],[6]]) (.forbid 1 2 6 (.system [[0],[1,7,8,9,10,11,12,2],[6]]) (.forbid 1 5 1 (.system [[0],[1,7,5,4,3,2],[6]]) (certificate_33_part_5))))))))

noncomputable def certificate_33_part_2 : FiniteCertificate := .forbid 1 6 5 (.system [[0],[1,7,8,9,10,11,6],[2]]) (.forbid 1 6 6 (.system [[0],[1,7,8,9,10,11,12,6],[2]]) (.forbid 5 6 1 (.system [[0],[1],[2,3,4,5,7,6]]) (.forbid 0 3 0 (.forbid 0 1 2 (.cycle [0,3,4,5,6,1,8,7]) (.forbid 0 1 3 (.cycle [0,3,2,6,1,9,8,7]) (.forbid 0 6 3 (.cycle [0,3,2,1,6,9,8,7]) (.forbid 1 6 3 (.cycle [1,0,3,2,6,9,8,7]) (certificate_33_part_3))))) (.forbid 0 3 2 (.system [[0,7,8,3,4,5,6],[1],[2]]) (.forbid 0 3 3 (.system [[0,7,8,9,3,2],[1],[6]]) (.forbid 0 2 2 (.system [[0,7,8,2,3,4,5,6],[1]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2],[1],[6]]) (certificate_33_part_4))))))))

noncomputable def certificate_33_part_1 : FiniteCertificate := .forbid 0 6 4 (.system [[0,7,8,9,10,6],[1],[2]]) (.forbid 0 6 5 (.system [[0,7,8,9,10,11,6],[1],[2]]) (.forbid 0 6 6 (.system [[0,7,8,9,10,11,12,6],[1],[2]]) (.forbid 1 2 1 (.system [[0],[1,7,2,3,4,5,6]]) (.forbid 1 3 1 (.system [[0],[1,7,3,4,5,6],[2]]) (.forbid 1 6 1 (.system [[0],[1,7,6,5,4,3,2]]) (.forbid 1 6 2 (.system [[0],[1,7,8,6,5,4,3,2]]) (.forbid 1 6 4 (.system [[0],[1,7,8,9,10,6],[2]]) (certificate_33_part_2))))))))

noncomputable def certificate_33 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1],[2,3,4,5,6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[2],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[2],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[2],[6]]) (.forbid 0 2 1 (.system [[0,7,2,3,4,5,6],[1]]) (.forbid 0 3 1 (.system [[0,7,3,4,5,6],[1],[2]]) (.forbid 0 6 1 (.system [[0,7,6,5,4,3,2],[1]]) (.forbid 0 6 2 (.system [[0,7,8,6,5,4,3,2],[1]]) (certificate_33_part_1))))))))

noncomputable def certificate_45 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1],[2],[3],[4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1],[2],[3],[4],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1],[2],[3],[4],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[2],[3],[4],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[2],[3],[4],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[2],[3],[4],[6]]) (.forbid 0 2 1 (.system [[0,7,2],[1],[3],[4,5,6]]) (.forbid 0 2 2 (.system [[0,7,8,2],[1],[3],[4],[6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2],[1],[3],[4],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2],[1],[3],[4],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2],[1],[3],[4],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2],[1],[3],[4],[6]]) (.forbid 0 3 1 (.system [[0,7,3],[1],[2],[4,5,6]]) (.forbid 0 3 2 (.system [[0,7,8,3],[1],[2],[4],[6]]) (.forbid 0 4 1 (.system [[0,7,4,5,6],[1],[2],[3]]) (.forbid 0 4 2 (.system [[0,7,8,4],[1],[2],[3],[6]]) (.forbid 0 5 1 (.system [[0,7,5,4],[1],[2],[3],[6]]) (.forbid 0 5 2 (.system [[0,7,8,5,4],[1],[2],[3],[6]]) (.forbid 0 6 1 (.system [[0,7,6,5,4],[1],[2],[3]]) (.forbid 1 2 1 (.system [[0],[1,7,2],[3],[4,5,6]]) (certificate_45_part_0))))))))))))))))))))

noncomputable def certificate_50_part_1_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((0,1,2) :: (((0,1,1) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (certificate_50_M))))))))))))))))

noncomputable def certificate_50_part_2_M : ForbiddenMatrix := ((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,3,1) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_50_part_1_M))))))))))))))))

noncomputable def certificate_50_part_3_M : ForbiddenMatrix := ((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,0) :: (((2,3,1) :: (((1,3,1) :: (((1,2,6) :: (((1,2,5) :: (certificate_50_part_2_M))))))))))))))))

noncomputable def certificate_50_part_4_M : ForbiddenMatrix := ((0,5,2) :: (((0,5,1) :: (((2,4,0) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((1,3,0) :: (((0,4,0) :: (certificate_50_part_3_M))))))))))))))))

noncomputable def certificate_50_part_5_M : ForbiddenMatrix := ((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (certificate_50_part_4_M))))))))))))))))

noncomputable def certificate_50_part_6_M : ForbiddenMatrix := ((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (((1,6,1) :: (((1,5,1) :: (((0,6,6) :: (((0,6,5) :: (certificate_50_part_5_M))))))))))))))))

noncomputable def certificate_51_part_1_M : ForbiddenMatrix := ((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (((0,1,1) :: (certificate_51_M))))))))))))))))

noncomputable def certificate_51_part_2_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,1) :: (((0,3,6) :: (((0,3,5) :: (certificate_51_part_1_M))))))))))))))))

noncomputable def certificate_51_part_3_M : ForbiddenMatrix := ((0,5,1) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((3,4,1) :: (((2,3,1) :: (((1,3,6) :: (certificate_51_part_2_M))))))))))))))

noncomputable def certificate_51_part_4_M : ForbiddenMatrix := ((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,4,0) :: (((3,4,1) :: (((2,3,1) :: (((1,3,6) :: (certificate_51_part_2_M))))))))))))))))

noncomputable def certificate_51_part_5_M : ForbiddenMatrix := ((0,5,1) :: (((0,5,0) :: (((0,3,0) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((0,6,1) :: (certificate_51_part_4_M))))))))))))))

noncomputable def certificate_51_part_6_M : ForbiddenMatrix := ((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((0,6,1) :: (certificate_51_part_4_M))))))))))))))))

noncomputable def certificate_51_part_7_M : ForbiddenMatrix := ((4,6,3) :: (((4,6,2) :: (((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,5,0) :: (((0,4,5) :: (certificate_51_part_6_M))))))))))))))))

noncomputable def certificate_51_part_8_M : ForbiddenMatrix := ((4,6,1) :: (((4,6,0) :: (((2,6,0) :: (((1,6,0) :: (((1,4,0) :: (((0,6,0) :: (((4,6,4) :: (certificate_51_part_7_M))))))))))))))

noncomputable def certificate_51_part_9_M : ForbiddenMatrix := ((1,6,2) :: (((1,4,3) :: (((1,4,2) :: (((1,6,1) :: (((1,5,0) :: (((1,4,0) :: (((0,5,1) :: (((4,6,4) :: (certificate_51_part_7_M))))))))))))))))

noncomputable def certificate_51_part_10_M : ForbiddenMatrix := ((4,6,1) :: (((2,4,1) :: (((1,4,1) :: (((0,1,2) :: (((5,6,1) :: (((4,6,6) :: (((1,6,3) :: (certificate_51_part_9_M))))))))))))))

noncomputable def certificate_51_part_11_M : ForbiddenMatrix := ((1,5,2) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,5,0) :: (((5,6,1) :: (((4,6,6) :: (((1,6,3) :: (certificate_51_part_9_M))))))))))))))))

noncomputable def certificate_51_part_12_M : ForbiddenMatrix := ((3,5,1) :: (((0,8,3) :: (((0,8,2) :: (((0,8,1) :: (((4,6,0) :: (((3,5,6) :: (((1,5,3) :: (certificate_51_part_11_M))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates009
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_279 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2],[3],[4],[5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[2],[3],[4],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[3],[4],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[2],[3],[4],[5]]) (.forbid 0 2 1 (.system [[0,6,2],[1],[3],[4],[5]]) (.forbid 0 2 2 (.system [[0,6,7,2],[1],[3],[4],[5]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[3],[4],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[3],[4],[5]]) (.forbid 0 3 1 (.system [[0,6,3],[1],[2],[4],[5]]) (.forbid 0 3 2 (.system [[0,6,7,3],[1],[2],[4],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3],[1],[2],[4],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3],[1],[2],[4],[5]]) (.forbid 1 2 1 (.system [[0],[1,6,2],[3],[4],[5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2],[3],[4],[5]]) (.forbid 1 2 3 (.system [[0],[1,6,7,8,2],[3],[4],[5]]) (.forbid 1 2 4 (.system [[0],[1,6,7,8,9,2],[3],[4],[5]]) (.forbid 1 3 1 (.system [[0],[1,6,3],[2],[4],[5]]) (.forbid 1 3 2 (.system [[0],[1,6,7,3],[2],[4],[5]]) (.forbid 1 3 3 (.system [[0],[1,6,7,8,3],[2],[4],[5]]) (.forbid 1 3 4 (.system [[0],[1,6,7,8,9,3],[2],[4],[5]]) (certificate_279_part_0))))))))))))))))))))

noncomputable def certificate_284_part_1_M : ForbiddenMatrix := ((0,3,1) :: (((0,1,6) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_284_M))))))))))))))))

noncomputable def certificate_284_part_2_M : ForbiddenMatrix := ((0,6,2) :: (((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((0,4,1) :: (certificate_284_part_1_M))))))))))))))))

noncomputable def certificate_284_part_3_M : ForbiddenMatrix := ((1,4,1) :: (((1,3,1) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (certificate_284_part_2_M))))))))))))))))

noncomputable def certificate_284_part_4_M : ForbiddenMatrix := ((1,6,3) :: (((1,6,2) :: (((1,5,6) :: (((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (certificate_284_part_3_M))))))))))))))))

noncomputable def certificate_284_part_5_M : ForbiddenMatrix := ((4,5,1) :: (((3,5,1) :: (((2,6,2) :: (((2,5,3) :: (((2,5,2) :: (((2,5,1) :: (((1,6,5) :: (((1,6,4) :: (certificate_284_part_4_M))))))))))))))))

noncomputable def certificate_284_part_6_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (certificate_284_part_5_M))))))))))))))

noncomputable def certificate_284_part_7_M : ForbiddenMatrix := ((0,3,2) :: (((0,2,6) :: (((0,5,0) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (certificate_284_part_5_M))))))))))))))))

noncomputable def certificate_284_part_8_M : ForbiddenMatrix := ((2,3,2) :: (((2,3,1) :: (((1,3,6) :: (((1,3,3) :: (((1,3,2) :: (((1,2,6) :: (((0,3,6) :: (((0,3,3) :: (certificate_284_part_7_M))))))))))))))))

noncomputable def certificate_284_part_9_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (((3,4,1) :: (((2,4,1) :: (((2,3,6) :: (((2,3,3) :: (certificate_284_part_8_M))))))))))))))

noncomputable def certificate_284_part_10_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (certificate_284_part_9_M))))))))))))))))

noncomputable def certificate_284_part_11_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((0,6,0) :: (((3,4,1) :: (((2,4,1) :: (((2,3,6) :: (((2,3,3) :: (certificate_284_part_8_M))))))))))))))

noncomputable def certificate_284_part_12_M : ForbiddenMatrix := ((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (certificate_284_part_11_M))))))))))))))))

noncomputable def certificate_284_part_13_M : ForbiddenMatrix := ((2,5,0) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,7,1) :: (((1,5,0) :: (((1,3,5) :: (((1,3,4) :: (certificate_284_part_12_M))))))))))))))))

noncomputable def certificate_284_part_14_M : ForbiddenMatrix := ((0,1,4) :: (((0,6,1) :: (((0,6,0) :: (((3,4,1) :: (((2,4,1) :: (((2,3,6) :: (((2,3,3) :: (certificate_284_part_8_M))))))))))))))

noncomputable def certificate_284_part_15_E : List (ℕ × ℕ) := certificate_284_part_14_E

noncomputable def certificate_284_part_15_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (certificate_284_part_14_M))))))))))))))))

noncomputable def certificate_284_part_16_M : ForbiddenMatrix := ((0,7,0) :: (((0,6,1) :: (((0,6,0) :: (((3,4,1) :: (((2,4,1) :: (((2,3,6) :: (((2,3,3) :: (certificate_284_part_8_M))))))))))))))

noncomputable def certificate_284_part_17_M : ForbiddenMatrix := ((1,2,4) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (certificate_284_part_16_M))))))))))))))))

noncomputable def certificate_284_part_18_M : ForbiddenMatrix := ((0,8,0) :: (((0,7,0) :: (((0,6,1) :: (((0,6,0) :: (((3,4,1) :: (((2,4,1) :: (((2,3,6) :: (((2,3,3) :: (certificate_284_part_8_M))))))))))))))))

noncomputable def certificate_284_part_19_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((0,4,6) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (certificate_284_part_18_M))))))))))))))))

noncomputable def certificate_284_part_20_M : ForbiddenMatrix := ((0,1,4) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((2,4,3) :: (((2,4,2) :: (certificate_284_part_19_M))))))))))))))

noncomputable def certificate_284_part_21_M : ForbiddenMatrix := ((0,9,0) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((2,4,3) :: (((2,4,2) :: (certificate_284_part_19_M))))))))))))))

noncomputable def certificate_284_part_22_M : ForbiddenMatrix := ((1,5,0) :: (((0,9,0) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((2,4,3) :: (((2,4,2) :: (certificate_284_part_19_M))))))))))))))))

noncomputable def certificate_284_part_23_M : ForbiddenMatrix := ((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (certificate_284_part_22_M))))))))))))))

noncomputable def certificate_284_part_24_M : ForbiddenMatrix := ((2,7,1) :: (((2,3,5) :: (((2,3,4) :: (((1,7,1) :: (((1,3,5) :: (((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (certificate_284_part_23_M))))))))))))))))

noncomputable def certificate_284_part_23 : FiniteCertificate := .forbid 1 2 4 (.cycle [1,6,5,4,0,3,10,2,14,13,12,11]) (.forbid 1 2 5 (.cycle [1,6,5,4,0,3,2,15,14,13,12,11]) (.forbid 1 3 4 (.cycle [1,6,5,4,0,2,10,3,14,13,12,11]) (.forbid 1 3 5 (.cycle [1,6,5,4,0,2,3,15,14,13,12,11]) (.forbid 1 7 1 (.cycle [1,6,5,4,0,2,3,10,9,8,7,11]) (.forbid 2 3 4 (.cycle [2,0,1,6,5,4,10,3,14,13,12,11]) (.forbid 2 3 5 (.cycle [2,0,1,6,5,4,3,15,14,13,12,11]) (.forbid 2 7 1 (.cycle [2,0,1,6,5,4,3,10,9,8,7,11]) (certificate_284_part_24))))))))

noncomputable def certificate_284_part_25_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (((1,6,0) :: (certificate_284_part_22_M))))))))))))))

noncomputable def certificate_284_part_26_M : ForbiddenMatrix := ((1,8,1) :: (((1,7,1) :: (((1,3,5) :: (((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,7,1) :: (certificate_284_part_25_M))))))))))))))))

noncomputable def certificate_284_part_27_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (((1,6,1) :: (((1,6,0) :: (certificate_284_part_22_M))))))))))))))

noncomputable def certificate_284_part_28_M : ForbiddenMatrix := ((2,6,1) :: (((2,3,5) :: (((2,3,4) :: (((1,3,5) :: (((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,3,5) :: (certificate_284_part_27_M))))))))))))))))

noncomputable def certificate_284_part_29_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (((1,7,0) :: (((1,6,1) :: (((1,6,0) :: (certificate_284_part_22_M))))))))))))))

noncomputable def certificate_284_part_30_M : ForbiddenMatrix := ((1,7,1) :: (((1,3,5) :: (((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (certificate_284_part_29_M))))))))))))))))

noncomputable def certificate_284_part_31_M : ForbiddenMatrix := ((0,4,5) :: (((0,1,5) :: (((0,1,4) :: (((1,8,0) :: (((1,7,0) :: (((1,6,1) :: (((1,6,0) :: (certificate_284_part_22_M))))))))))))))

noncomputable def certificate_284_part_32_M : ForbiddenMatrix := ((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,1) :: (((1,6,0) :: (certificate_284_part_22_M))))))))))))))))

noncomputable def certificate_284_part_33_M : ForbiddenMatrix := ((3,6,1) :: (((2,6,1) :: (((0,2,5) :: (((0,2,4) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_284_part_32_M))))))))))))))

noncomputable def certificate_284_part_34_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (((2,5,0) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_284_part_32_M))))))))))))))

noncomputable def certificate_284_part_35_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (certificate_284_part_34_M))))))))))))))))

noncomputable def certificate_284_part_36_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((2,6,0) :: (((2,5,0) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_284_part_32_M))))))))))))))

noncomputable def certificate_284_part_37_M : ForbiddenMatrix := ((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (certificate_284_part_36_M))))))))))))))))

noncomputable def certificate_284_part_38_M : ForbiddenMatrix := ((2,8,1) :: (((2,7,1) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,7,1) :: (((1,3,5) :: (((1,3,4) :: (certificate_284_part_37_M))))))))))))))))

noncomputable def certificate_284_part_39_M : ForbiddenMatrix := ((0,1,4) :: (((2,6,1) :: (((2,6,0) :: (((2,5,0) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_284_part_32_M))))))))))))))

noncomputable def certificate_284_part_40_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (certificate_284_part_39_M))))))))))))))))

noncomputable def certificate_284_part_41_M : ForbiddenMatrix := ((2,7,0) :: (((2,6,1) :: (((2,6,0) :: (((2,5,0) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_284_part_32_M))))))))))))))

noncomputable def certificate_284_part_42_M : ForbiddenMatrix := ((1,2,4) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (certificate_284_part_41_M))))))))))))))))

noncomputable def certificate_284_part_43_M : ForbiddenMatrix := ((2,8,0) :: (((2,7,0) :: (((2,6,1) :: (((2,6,0) :: (((2,5,0) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_284_part_32_M))))))))))))))))

noncomputable def certificate_284_part_44_M : ForbiddenMatrix := ((2,4,5) :: (((0,8,1) :: (((0,4,5) :: (((0,2,5) :: (((0,2,4) :: (((2,4,6) :: (((2,4,4) :: (certificate_284_part_43_M))))))))))))))

noncomputable def certificate_284_part_45_M : ForbiddenMatrix := ((3,5,6) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((2,9,0) :: (((2,4,6) :: (((2,4,4) :: (certificate_284_part_43_M))))))))))))))))

noncomputable def certificate_284_part_46_M : ForbiddenMatrix := ((3,6,1) :: (((0,3,5) :: (((0,3,4) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (certificate_284_part_45_M))))))))))))))

noncomputable def certificate_284_part_47_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((3,5,0) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (certificate_284_part_45_M))))))))))))))

noncomputable def certificate_284_part_48_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,3,5) :: (((0,3,4) :: (((0,2,5) :: (((0,2,4) :: (certificate_284_part_47_M))))))))))))))))

noncomputable def certificate_284_part_49_M : ForbiddenMatrix := ((1,9,1) :: (((0,9,1) :: (((3,6,0) :: (((3,5,0) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (certificate_284_part_45_M))))))))))))))))

noncomputable def certificate_284_part_50_M : ForbiddenMatrix := ((1,2,4) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((3,9,1) :: (((3,4,2) :: (((2,9,1) :: (certificate_284_part_49_M))))))))))))))

noncomputable def certificate_284_part_51_M : ForbiddenMatrix := ((4,6,5) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((4,6,0) :: (((3,9,1) :: (((3,4,2) :: (((2,9,1) :: (certificate_284_part_49_M))))))))))))))))

noncomputable def certificate_284_part_22 : FiniteCertificate := .forbid 1 6 0 (.forbid 0 1 4 (.cycle [0,2,3,10,4,5,6,1,14,13,12,11]) (.forbid 0 1 5 (.cycle [0,2,3,4,5,6,1,15,14,13,12,11]) (.forbid 0 2 4 (.cycle [0,1,6,5,4,3,10,2,14,13,12,11]) (.forbid 0 2 5 (.cycle [0,1,6,5,4,3,2,15,14,13,12,11]) (.forbid 0 3 4 (.cycle [0,1,6,5,4,2,10,3,14,13,12,11]) (.forbid 0 3 5 (.cycle [0,1,6,5,4,2,3,15,14,13,12,11]) (.forbid 0 7 1 (.cycle [0,1,6,5,4,2,3,10,9,8,7,11]) (certificate_284_part_23)))))))) (.forbid 1 6 1 (.forbid 0 1 4 (.cycle [0,2,3,4,5,6,11,1,15,14,13,12]) (.forbid 0 1 5 (.cycle [0,2,4,5,6,11,1,16,15,14,13,12]) (.forbid 0 2 4 (.cycle [0,1,11,6,5,4,3,2,15,14,13,12]) (.forbid 0 2 5 (.cycle [0,1,11,6,5,4,2,16,15,14,13,12]) (.forbid 0 3 4 (.cycle [0,1,11,6,5,4,2,3,15,14,13,12]) (.forbid 0 3 5 (.cycle [0,1,11,6,5,4,3,16,15,14,13,12]) (certificate_284_part_25))))))) (.forbid 1 7 0 (.forbid 0 1 4 (.cycle [0,2,3,4,5,6,7,1,14,13,12,11]) (.forbid 0 1 5 (.cycle [0,2,4,5,6,7,1,15,14,13,12,11]) (.forbid 0 2 4 (.cycle [0,1,7,6,5,4,3,2,14,13,12,11]) (.forbid 0 2 5 (.cycle [0,1,7,6,5,4,2,15,14,13,12,11]) (.forbid 0 3 4 (.cycle [0,1,7,6,5,4,2,3,14,13,12,11]) (certificate_284_part_27)))))) (.forbid 1 8 0 (.forbid 0 1 4 (.cycle [0,2,3,4,10,9,8,1,14,13,12,11]) (.forbid 0 1 5 (.cycle [0,2,3,10,9,8,1,15,14,13,12,11]) (.forbid 0 2 4 (.cycle [0,1,8,7,6,5,4,2,14,13,12,11]) (.forbid 0 2 5 (.cycle [0,1,8,9,10,3,2,15,14,13,12,11]) (certificate_284_part_29))))) (.forbid 1 9 0 (.forbid 0 1 4 (.cycle [0,4,5,6,7,8,9,1,14,13,12,11]) (.forbid 0 1 5 (.cycle [0,2,3,4,10,9,1,15,14,13,12,11]) (.forbid 0 4 5 (.cycle [0,1,9,10,2,3,4,15,14,13,12,11]) (certificate_284_part_31)))) (.forbid 2 5 4 (.system [[0],[1],[2,11,12,13,14,5,6,7,8,9,10],[3],[4]]) (.forbid 2 5 5 (.system [[0],[1],[2,11,12,13,14,15,5,4],[3],[10]]) (.forbid 2 5 6 (.system [[0],[1],[2,11,12,13,14,15,16,5,4],[3],[10]]) (certificate_284_part_32))))))))

noncomputable def certificate_284_part_19 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1],[2,11,12,4,5,6,7,8,9,10],[3]]) (.forbid 2 4 3 (.system [[0],[1],[2,11,12,13,4,5,6,7,8,9,10],[3]]) (.forbid 4 5 2 (.system [[0],[1],[2],[3],[4,11,12,5,6,7,8,9,10]]) (.forbid 4 5 3 (.system [[0],[1],[2],[3],[4,11,12,13,5,6,7,8,9,10]]) (.forbid 4 5 4 (.system [[0],[1],[2],[3],[4,11,12,13,14,5,6,7,8,9,10]]) (.forbid 4 5 5 (.system [[0],[1],[2],[3],[4,11,12,13,14,15,5,6,7,8,9,10]]) (.forbid 0 9 0 (.forbid 0 1 4 (.cycle [0,9,8,7,6,5,4,1,14,13,12,11]) (certificate_284_part_20)) (.forbid 1 5 0 (certificate_284_part_21) (certificate_284_part_22))))))))

noncomputable def certificate_284_part_18 : FiniteCertificate := .forbid 0 4 2 (.system [[0,11,12,4,5,6,7,8,9,10],[1],[2],[3]]) (.forbid 0 4 3 (.system [[0,11,12,13,4,5,6,7,8,9,10],[1],[2],[3]]) (.forbid 0 4 4 (.system [[0,11,12,13,14,4,5,6,7,8,9,10],[1],[2],[3]]) (.forbid 0 4 6 (.system [[0,11,12,13,14,15,16,4],[1],[2],[3],[10]]) (.forbid 1 4 2 (.system [[0],[1,11,12,4,5,6,7,8,9,10],[2],[3]]) (.forbid 1 4 3 (.system [[0],[1,11,12,13,4,5,6,7,8,9,10],[2],[3]]) (.forbid 1 4 4 (.system [[0],[1,11,12,13,14,4,5,6,7,8,9,10],[2],[3]]) (.forbid 1 4 6 (.system [[0],[1,11,12,13,14,15,16,4],[2],[3],[10]]) (certificate_284_part_19))))))))

noncomputable def certificate_284_part_8 : FiniteCertificate := .forbid 2 3 3 (.system [[0],[1],[2,11,12,13,3],[4,5,6,7,8,9,10]]) (.forbid 2 3 6 (.system [[0],[1],[2,11,12,13,14,15,16,3],[4],[10]]) (.forbid 2 4 1 (.system [[0],[1],[2,11,4,5,6,7,8,9,10],[3]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,11,4,5,6,7,8,9,10]]) (.forbid 0 6 0 (.forbid 0 1 4 (.cycle [0,6,5,4,2,3,10,1,14,13,12,11]) (.forbid 0 1 5 (.cycle [0,6,5,4,2,3,1,15,14,13,12,11]) (.forbid 0 2 4 (.cycle [0,6,5,4,1,3,10,2,14,13,12,11]) (certificate_284_part_9)))) (.forbid 0 6 1 (.forbid 0 1 4 (.cycle [0,11,6,5,4,2,3,1,15,14,13,12]) (.forbid 0 1 5 (.cycle [0,11,6,5,4,2,1,16,15,14,13,12]) (certificate_284_part_11))) (.forbid 0 7 0 (.forbid 0 1 4 (.cycle [0,7,6,5,4,2,3,1,14,13,12,11]) (certificate_284_part_14)) (.forbid 0 8 0 (certificate_284_part_16) (certificate_284_part_18))))))))

noncomputable def certificate_284_part_7 : FiniteCertificate := .forbid 0 3 3 (.system [[0,11,12,13,3],[1],[2],[4,5,6,7,8,9,10]]) (.forbid 0 3 6 (.system [[0,11,12,13,14,15,16,3],[1],[2],[4],[10]]) (.forbid 1 2 6 (.system [[0],[1,11,12,13,14,15,16,2],[3],[4],[10]]) (.forbid 1 3 2 (.system [[0],[1,11,12,3],[2],[4,5,6,7,8,9,10]]) (.forbid 1 3 3 (.system [[0],[1,11,12,13,3],[2],[4,5,6,7,8,9,10]]) (.forbid 1 3 6 (.system [[0],[1,11,12,13,14,15,16,3],[2],[4],[10]]) (.forbid 2 3 1 (.system [[0],[1],[2,11,3],[4,5,6,7,8,9,10]]) (.forbid 2 3 2 (.system [[0],[1],[2,11,12,3],[4,5,6,7,8,9,10]]) (certificate_284_part_8))))))))

noncomputable def certificate_284_part_5 : FiniteCertificate := .forbid 5 6 1 (.system [[0],[1],[2],[3],[4,5,11,6,7,8,9,10]]) (.forbid 5 6 2 (.system [[0],[1],[2],[3],[4,5,11,12,6,7,8,9,10]]) (.forbid 5 6 3 (.system [[0],[1],[2],[3],[4,5,11,12,13,6,7,8,9,10]]) (.forbid 5 6 4 (.system [[0],[1],[2],[3],[4,5,11,12,13,14,6,7,8,9,10]]) (.forbid 5 6 5 (.system [[0],[1],[2],[3],[4,5,11,12,13,14,15,6,7,8,9,10]]) (.forbid 0 5 0 (.forbid 0 1 4 (.cycle [0,5,6,7,8,9,10,1,14,13,12,11]) (.forbid 0 1 5 (.cycle [0,5,4,2,3,10,1,15,14,13,12,11]) (certificate_284_part_6))) (.forbid 0 2 6 (.system [[0,11,12,13,14,15,16,2],[1],[3],[4],[10]]) (.forbid 0 3 2 (.system [[0,11,12,3],[1],[2],[4,5,6,7,8,9,10]]) (certificate_284_part_7))))))))

noncomputable def certificate_284_part_4 : FiniteCertificate := .forbid 1 6 4 (.system [[0],[1,11,12,13,14,6,5,4],[2],[3],[10]]) (.forbid 1 6 5 (.system [[0],[1,11,12,13,14,15,6,5,4],[2],[3],[10]]) (.forbid 2 5 1 (.system [[0],[1],[2,11,5,6,7,8,9,10],[3],[4]]) (.forbid 2 5 2 (.system [[0],[1],[2,11,12,5,6,7,8,9,10],[3],[4]]) (.forbid 2 5 3 (.system [[0],[1],[2,11,12,13,5,6,7,8,9,10],[3],[4]]) (.forbid 2 6 2 (.system [[0],[1],[2,11,12,6,7,8,9,10],[3],[4]]) (.forbid 3 5 1 (.system [[0],[1],[2],[3,11,5,6,7,8,9,10],[4]]) (.forbid 4 5 1 (.system [[0],[1],[2],[3],[4,11,5,6,7,8,9,10]]) (certificate_284_part_5))))))))

noncomputable def certificate_284_part_3 : FiniteCertificate := .forbid 1 5 1 (.system [[0],[1,11,5,6,7,8,9,10],[2],[3],[4]]) (.forbid 1 5 2 (.system [[0],[1,11,12,5,6,7,8,9,10],[2],[3],[4]]) (.forbid 1 5 3 (.system [[0],[1,11,12,13,5,6,7,8,9,10],[2],[3],[4]]) (.forbid 1 5 4 (.system [[0],[1,11,12,13,14,5,6,7,8,9,10],[2],[3],[4]]) (.forbid 1 5 5 (.system [[0],[1,11,12,13,14,15,5,4],[2],[3],[10]]) (.forbid 1 5 6 (.system [[0],[1,11,12,13,14,15,16,5,4],[2],[3],[10]]) (.forbid 1 6 2 (.system [[0],[1,11,12,6,7,8,9,10],[2],[3],[4]]) (.forbid 1 6 3 (.system [[0],[1,11,12,13,6,7,8,9,10],[2],[3],[4]]) (certificate_284_part_4))))))))

noncomputable def certificate_284_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,11,12,13,6,7,8,9,10],[1],[2],[3],[4]]) (.forbid 0 6 4 (.system [[0,11,12,13,14,6,5,4],[1],[2],[3],[10]]) (.forbid 0 6 5 (.system [[0,11,12,13,14,15,6,5,4],[1],[2],[3],[10]]) (.forbid 1 2 1 (.system [[0],[1,11,2],[3],[4,5,6,7,8,9,10]]) (.forbid 1 2 2 (.system [[0],[1,11,12,2],[3],[4,5,6,7,8,9,10]]) (.forbid 1 2 3 (.system [[0],[1,11,12,13,2],[3],[4,5,6,7,8,9,10]]) (.forbid 1 3 1 (.system [[0],[1,11,3],[2],[4,5,6,7,8,9,10]]) (.forbid 1 4 1 (.system [[0],[1,11,4,5,6,7,8,9,10],[2],[3]]) (certificate_284_part_3))))))))

noncomputable def certificate_284_part_1 : FiniteCertificate := .forbid 0 4 1 (.system [[0,11,4,5,6,7,8,9,10],[1],[2],[3]]) (.forbid 0 5 1 (.system [[0,11,5,6,7,8,9,10],[1],[2],[3],[4]]) (.forbid 0 5 2 (.system [[0,11,12,5,6,7,8,9,10],[1],[2],[3],[4]]) (.forbid 0 5 3 (.system [[0,11,12,13,5,6,7,8,9,10],[1],[2],[3],[4]]) (.forbid 0 5 4 (.system [[0,11,12,13,14,5,6,7,8,9,10],[1],[2],[3],[4]]) (.forbid 0 5 5 (.system [[0,11,12,13,14,15,5,4],[1],[2],[3],[10]]) (.forbid 0 5 6 (.system [[0,11,12,13,14,15,16,5,4],[1],[2],[3],[10]]) (.forbid 0 6 2 (.system [[0,11,12,6,7,8,9,10],[1],[2],[3],[4]]) (certificate_284_part_2))))))))

noncomputable def certificate_284 : FiniteCertificate := .forbid 0 1 1 (.system [[0,11,1],[2],[3],[4,5,6,7,8,9,10]]) (.forbid 0 1 2 (.system [[0,11,12,1],[2],[3],[4,5,6,7,8,9,10]]) (.forbid 0 1 3 (.system [[0,11,12,13,1],[2],[3],[4,5,6,7,8,9,10]]) (.forbid 0 2 1 (.system [[0,11,2],[1],[3],[4,5,6,7,8,9,10]]) (.forbid 0 2 2 (.system [[0,11,12,2],[1],[3],[4,5,6,7,8,9,10]]) (.forbid 0 2 3 (.system [[0,11,12,13,2],[1],[3],[4,5,6,7,8,9,10]]) (.forbid 0 1 6 (.system [[0,11,12,13,14,15,16,1],[2],[3],[4],[10]]) (.forbid 0 3 1 (.system [[0,11,3],[1],[2],[4,5,6,7,8,9,10]]) (certificate_284_part_1))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_367_part_1_M : ForbiddenMatrix := ((0,3,2) :: (((0,3,1) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_367_M))))))))))))))))

noncomputable def certificate_367_part_2_M : ForbiddenMatrix := ((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,3,3) :: (certificate_367_part_1_M))))))))))))))))

noncomputable def certificate_367_part_3_M : ForbiddenMatrix := ((1,3,1) :: (((1,2,2) :: (((1,2,1) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,5,5) :: (((0,5,4) :: (certificate_367_part_2_M))))))))))))))))

noncomputable def certificate_367_part_4_M : ForbiddenMatrix := ((1,5,2) :: (((1,5,1) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,3,3) :: (((1,3,2) :: (certificate_367_part_3_M))))))))))))))))

noncomputable def certificate_367_part_5_M : ForbiddenMatrix := ((2,4,1) :: (((2,3,1) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (certificate_367_part_4_M))))))))))))))))

noncomputable def certificate_367_part_6_M : ForbiddenMatrix := ((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (((2,6,2) :: (((2,5,3) :: (((2,5,2) :: (((2,5,1) :: (((2,4,2) :: (certificate_367_part_5_M))))))))))))))))

noncomputable def certificate_367_part_7_M : ForbiddenMatrix := ((4,5,2) :: (((4,5,1) :: (((3,6,3) :: (((3,6,2) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (certificate_367_part_6_M))))))))))))))))

noncomputable def certificate_367_part_8_M : ForbiddenMatrix := ((5,6,2) :: (((5,6,1) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (certificate_367_part_7_M))))))))))))))))

noncomputable def certificate_367_part_9_M : ForbiddenMatrix := ((2,6,1) :: (((1,6,1) :: (((0,6,1) :: (((0,1,4) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (certificate_367_part_8_M))))))))))))))

noncomputable def certificate_367_part_10_M : ForbiddenMatrix := ((2,3,2) :: (((1,5,6) :: (((1,2,3) :: (((0,5,6) :: (((0,5,0) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (certificate_367_part_8_M))))))))))))))))

noncomputable def certificate_367_part_11_M : ForbiddenMatrix := ((0,1,4) :: (((3,5,6) :: (((3,5,5) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,3,3) :: (certificate_367_part_10_M))))))))))))))

noncomputable def certificate_367_part_12_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (certificate_367_part_11_M))))))))))))))))

noncomputable def certificate_367_part_13_M : ForbiddenMatrix := ((1,7,1) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (certificate_367_part_12_M))))))))))))))))

noncomputable def certificate_367_part_14_M : ForbiddenMatrix := ((0,6,0) :: (((3,5,6) :: (((3,5,5) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,3,3) :: (certificate_367_part_10_M))))))))))))))

noncomputable def certificate_367_part_15_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_367_part_14_M))))))))))))))))

noncomputable def certificate_367_part_16_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,7,1) :: (((0,3,6) :: (certificate_367_part_15_M))))))))))))))))

noncomputable def certificate_367_part_17_M : ForbiddenMatrix := ((2,5,0) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,7,1) :: (((1,5,0) :: (((1,3,6) :: (certificate_367_part_16_M))))))))))))))))

noncomputable def certificate_367_part_18_M : ForbiddenMatrix := ((0,6,1) :: (((0,6,0) :: (((3,5,6) :: (((3,5,5) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,3,3) :: (certificate_367_part_10_M))))))))))))))))

noncomputable def certificate_367_part_19_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((3,4,4) :: (((2,4,4) :: (((2,4,3) :: (certificate_367_part_18_M))))))))))))))

noncomputable def certificate_367_part_20_M : ForbiddenMatrix := ((1,2,4) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (certificate_367_part_19_M))))))))))))))))

noncomputable def certificate_367_part_21_M : ForbiddenMatrix := ((1,6,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (certificate_367_part_20_M))))))))))))))))

noncomputable def certificate_367_part_22_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,6,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (certificate_367_part_21_M))))))))))))))))

noncomputable def certificate_367_part_23_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,7,0) :: (((3,4,4) :: (((2,4,4) :: (((2,4,3) :: (certificate_367_part_18_M))))))))))))))

noncomputable def certificate_367_part_24_M : ForbiddenMatrix := ((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (certificate_367_part_23_M))))))))))))))))

noncomputable def certificate_367_part_25_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (certificate_367_part_24_M))))))))))))))))

noncomputable def certificate_367_part_26_M : ForbiddenMatrix := ((2,7,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,7,1) :: (((1,4,6) :: (certificate_367_part_25_M))))))))))))))))

noncomputable def certificate_367_part_27_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((0,8,0) :: (((0,7,0) :: (((3,4,4) :: (((2,4,4) :: (((2,4,3) :: (certificate_367_part_18_M))))))))))))))

noncomputable def certificate_367_part_28_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (certificate_367_part_27_M))))))))))))))))

noncomputable def certificate_367_part_29_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,4,6) :: (certificate_367_part_28_M))))))))))))))))

noncomputable def certificate_367_part_30_M : ForbiddenMatrix := ((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,4,6) :: (((1,4,5) :: (certificate_367_part_29_M))))))))))))))))

noncomputable def certificate_367_part_31_M : ForbiddenMatrix := ((0,1,4) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,4) :: (((2,4,4) :: (((2,4,3) :: (certificate_367_part_18_M))))))))))))))

noncomputable def certificate_367_part_32_M : ForbiddenMatrix := ((1,5,0) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,4) :: (((2,4,4) :: (((2,4,3) :: (certificate_367_part_18_M))))))))))))))

noncomputable def certificate_367_part_33_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_367_part_32_M))))))))))))))))

noncomputable def certificate_367_part_34_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,3,6) :: (certificate_367_part_33_M))))))))))))))))

noncomputable def certificate_367_part_35_M : ForbiddenMatrix := ((1,6,0) :: (((1,5,0) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,4) :: (((2,4,4) :: (((2,4,3) :: (certificate_367_part_18_M))))))))))))))))

noncomputable def certificate_367_part_36_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_367_part_35_M))))))))))))))

noncomputable def certificate_367_part_37_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,7,1) :: (((0,3,6) :: (((0,3,5) :: (certificate_367_part_36_M))))))))))))))))

noncomputable def certificate_367_part_38_M : ForbiddenMatrix := ((2,5,0) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,7,1) :: (((1,3,6) :: (((1,3,5) :: (certificate_367_part_37_M))))))))))))))))

noncomputable def certificate_367_part_39_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((1,6,1) :: (certificate_367_part_35_M))))))))))))))

noncomputable def certificate_367_part_40_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_367_part_39_M))))))))))))))))

noncomputable def certificate_367_part_41_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (certificate_367_part_40_M))))))))))))))))

noncomputable def certificate_367_part_42_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((1,7,0) :: (((1,6,1) :: (certificate_367_part_35_M))))))))))))))

noncomputable def certificate_367_part_43_M : ForbiddenMatrix := ((1,2,4) :: (((0,7,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (certificate_367_part_42_M))))))))))))))))

noncomputable def certificate_367_part_44_M : ForbiddenMatrix := ((1,7,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (certificate_367_part_43_M))))))))))))))))

noncomputable def certificate_367_part_45_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (certificate_367_part_44_M))))))))))))))))

noncomputable def certificate_367_part_46_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((1,8,0) :: (((1,7,0) :: (((1,6,1) :: (certificate_367_part_35_M))))))))))))))

noncomputable def certificate_367_part_47_M : ForbiddenMatrix := ((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (certificate_367_part_46_M))))))))))))))))

noncomputable def certificate_367_part_48_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (certificate_367_part_47_M))))))))))))))))

noncomputable def certificate_367_part_49_M : ForbiddenMatrix := ((3,4,5) :: (((2,8,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (certificate_367_part_48_M))))))))))))))))

noncomputable def certificate_367_part_50_M : ForbiddenMatrix := ((0,2,4) :: (((2,6,4) :: (((2,6,3) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,1) :: (certificate_367_part_35_M))))))))))))))

noncomputable def certificate_367_part_51_M : ForbiddenMatrix := ((2,5,0) :: (((2,6,4) :: (((2,6,3) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,1) :: (certificate_367_part_35_M))))))))))))))

noncomputable def certificate_367_part_52_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_367_part_51_M))))))))))))))))

noncomputable def certificate_367_part_53_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,3,6) :: (certificate_367_part_52_M))))))))))))))))

noncomputable def certificate_367_part_54_M : ForbiddenMatrix := ((2,6,0) :: (((2,5,0) :: (((2,6,4) :: (((2,6,3) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,1) :: (certificate_367_part_35_M))))))))))))))))

noncomputable def certificate_367_part_55_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_367_part_54_M))))))))))))))

noncomputable def certificate_367_part_56_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,7,1) :: (((0,3,6) :: (((0,3,5) :: (certificate_367_part_55_M))))))))))))))))

noncomputable def certificate_367_part_57_M : ForbiddenMatrix := ((2,7,1) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,7,1) :: (((1,3,6) :: (((1,3,5) :: (certificate_367_part_56_M))))))))))))))))

noncomputable def certificate_367_part_58_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((2,6,1) :: (certificate_367_part_54_M))))))))))))))

noncomputable def certificate_367_part_59_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_367_part_58_M))))))))))))))))

noncomputable def certificate_367_part_60_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (certificate_367_part_59_M))))))))))))))))

noncomputable def certificate_367_part_61_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((2,7,0) :: (((2,6,1) :: (certificate_367_part_54_M))))))))))))))

noncomputable def certificate_367_part_62_M : ForbiddenMatrix := ((1,2,4) :: (((0,7,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (certificate_367_part_61_M))))))))))))))))

noncomputable def certificate_367_part_63_M : ForbiddenMatrix := ((1,7,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (certificate_367_part_62_M))))))))))))))))

noncomputable def certificate_367_part_64_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (certificate_367_part_63_M))))))))))))))))

noncomputable def certificate_367_part_65_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((2,8,0) :: (((2,7,0) :: (((2,6,1) :: (certificate_367_part_54_M))))))))))))))

noncomputable def certificate_367_part_66_M : ForbiddenMatrix := ((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (certificate_367_part_65_M))))))))))))))))

noncomputable def certificate_367_part_67_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (certificate_367_part_66_M))))))))))))))))

noncomputable def certificate_367_part_68_M : ForbiddenMatrix := ((3,4,5) :: (((2,8,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (certificate_367_part_67_M))))))))))))))))

noncomputable def certificate_367_part_69_M : ForbiddenMatrix := ((3,6,1) :: (((0,3,4) :: (((3,6,4) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,1) :: (certificate_367_part_54_M))))))))))))))

noncomputable def certificate_367_part_70_M : ForbiddenMatrix := ((0,1,4) :: (((3,5,0) :: (((3,6,4) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,1) :: (certificate_367_part_54_M))))))))))))))

noncomputable def certificate_367_part_71_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (certificate_367_part_70_M))))))))))))))))

noncomputable def certificate_367_part_72_M : ForbiddenMatrix := ((1,7,1) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (certificate_367_part_71_M))))))))))))))))

noncomputable def certificate_367_part_73_M : ForbiddenMatrix := ((0,10,1) :: (((3,6,0) :: (((3,5,0) :: (((3,6,4) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,1) :: (certificate_367_part_54_M))))))))))))))))

noncomputable def certificate_367_part_74_M : ForbiddenMatrix := ((0,11,4) :: (((0,11,3) :: (((0,11,2) :: (((0,11,1) :: (((0,10,5) :: (((0,10,4) :: (((0,10,3) :: (((0,10,2) :: (certificate_367_part_73_M))))))))))))))))

noncomputable def certificate_367_part_75_M : ForbiddenMatrix := ((1,11,3) :: (((1,11,2) :: (((1,11,1) :: (((1,10,5) :: (((1,10,4) :: (((1,10,3) :: (((1,10,2) :: (((1,10,1) :: (certificate_367_part_74_M))))))))))))))))

noncomputable def certificate_367_part_76_M : ForbiddenMatrix := ((2,11,2) :: (((2,11,1) :: (((2,10,5) :: (((2,10,4) :: (((2,10,3) :: (((2,10,2) :: (((2,10,1) :: (((1,11,4) :: (certificate_367_part_75_M))))))))))))))))

noncomputable def certificate_367_part_77_M : ForbiddenMatrix := ((3,11,1) :: (((3,10,5) :: (((3,10,4) :: (((3,10,3) :: (((3,10,2) :: (((3,10,1) :: (((2,11,4) :: (((2,11,3) :: (certificate_367_part_76_M))))))))))))))))

noncomputable def certificate_367_part_78_M : ForbiddenMatrix := ((10,11,4) :: (((10,11,3) :: (((10,11,2) :: (((10,11,1) :: (((9,10,1) :: (((3,11,4) :: (((3,11,3) :: (((3,11,2) :: (certificate_367_part_77_M))))))))))))))))

noncomputable def certificate_367_part_79_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((0,11,5) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((10,11,5) :: (certificate_367_part_78_M))))))))))))))

noncomputable def certificate_367_part_80_M : ForbiddenMatrix := ((3,6,1) :: (((0,4,5) :: (((0,3,4) :: (((0,2,4) :: (((0,6,5) :: (((4,6,0) :: (((10,11,5) :: (certificate_367_part_78_M))))))))))))))

noncomputable def certificate_376_part_1_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,2) :: (((0,1,1) :: (((0,3,5) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_376_M))))))))))))))))

noncomputable def certificate_376_part_2_M : ForbiddenMatrix := ((0,3,6) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,2,2) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (certificate_376_part_1_M))))))))))))))))

noncomputable def certificate_376_part_3_M : ForbiddenMatrix := ((1,2,1) :: (((0,6,1) :: (((0,4,6) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_376_part_2_M))))))))))))))))

noncomputable def certificate_376_part_4_M : ForbiddenMatrix := ((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((1,2,2) :: (certificate_376_part_3_M))))))))))))))))

noncomputable def certificate_376_part_5_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,3,6) :: (((1,3,5) :: (certificate_376_part_4_M))))))))))))))))

noncomputable def certificate_376_part_6_M : ForbiddenMatrix := ((2,4,1) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,6,1) :: (certificate_376_part_5_M))))))))))))))))

noncomputable def certificate_376_part_7_M : ForbiddenMatrix := ((3,4,2) :: (((3,4,1) :: (((2,6,1) :: (((2,4,6) :: (((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (certificate_376_part_6_M))))))))))))))))

noncomputable def certificate_376_part_8_M : ForbiddenMatrix := ((0,1,3) :: (((4,8,1) :: (((4,5,1) :: (((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (certificate_376_part_7_M))))))))))))))

noncomputable def certificate_376_part_9_M : ForbiddenMatrix := ((0,8,1) :: (((0,4,0) :: (((4,8,1) :: (((4,5,1) :: (((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (certificate_376_part_7_M))))))))))))))))

noncomputable def certificate_376_part_10_M : ForbiddenMatrix := ((3,6,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((3,8,1) :: (((2,8,1) :: (((1,8,1) :: (certificate_376_part_9_M))))))))))))))

noncomputable def certificate_376_part_11_M : ForbiddenMatrix := ((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,5,0) :: (((3,8,1) :: (((2,8,1) :: (((1,8,1) :: (certificate_376_part_9_M))))))))))))))))

noncomputable def certificate_376_part_12_M : ForbiddenMatrix := ((4,6,2) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (certificate_376_part_11_M))))))))))))))))

noncomputable def certificate_376_part_13_M : ForbiddenMatrix := ((1,6,0) :: (((1,4,0) :: (((0,7,1) :: (((0,6,0) :: (((0,1,3) :: (((4,6,4) :: (((4,6,3) :: (certificate_376_part_12_M))))))))))))))

noncomputable def certificate_376_part_14_M : ForbiddenMatrix := ((4,6,0) :: (((3,7,1) :: (((3,6,2) :: (((3,6,1) :: (((3,6,0) :: (((2,6,0) :: (((2,4,0) :: (((1,7,1) :: (certificate_376_part_13_M))))))))))))))))

noncomputable def certificate_376_part_15_M : ForbiddenMatrix := ((0,1,3) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((4,6,4) :: (((4,6,3) :: (certificate_376_part_12_M))))))))))))))

noncomputable def certificate_376_part_16_M : ForbiddenMatrix := ((0,6,0) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((4,6,4) :: (((4,6,3) :: (certificate_376_part_12_M))))))))))))))

noncomputable def certificate_376_part_17_M : ForbiddenMatrix := ((0,8,0) :: (((0,6,0) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((4,6,4) :: (((4,6,3) :: (certificate_376_part_12_M))))))))))))))))

noncomputable def certificate_376_part_18_M : ForbiddenMatrix := ((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((0,9,0) :: (((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (certificate_376_part_17_M))))))))))))))

noncomputable def certificate_376_part_19_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((1,4,0) :: (((0,9,0) :: (((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (certificate_376_part_17_M))))))))))))))

noncomputable def certificate_376_part_20_M : ForbiddenMatrix := ((0,1,3) :: (((1,5,0) :: (((1,4,0) :: (((0,9,0) :: (((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (certificate_376_part_17_M))))))))))))))

noncomputable def certificate_376_part_21_M : ForbiddenMatrix := ((1,8,0) :: (((1,5,0) :: (((1,4,0) :: (((0,9,0) :: (((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (certificate_376_part_17_M))))))))))))))

noncomputable def certificate_376_part_22_M : ForbiddenMatrix := ((2,4,0) :: (((1,8,0) :: (((1,5,0) :: (((1,4,0) :: (((0,9,0) :: (((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (certificate_376_part_17_M))))))))))))))))

noncomputable def certificate_376_part_23_M : ForbiddenMatrix := ((2,7,1) :: (((1,7,1) :: (((1,2,3) :: (((0,7,1) :: (((0,2,3) :: (((0,1,3) :: (((2,5,0) :: (certificate_376_part_22_M))))))))))))))

noncomputable def certificate_376_part_24_M : ForbiddenMatrix := ((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (((2,6,2) :: (((1,6,6) :: (((0,6,6) :: (((2,8,0) :: (((2,5,0) :: (certificate_376_part_22_M))))))))))))))))

noncomputable def certificate_376_part_25_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((6,7,1) :: (((5,6,1) :: (((4,6,6) :: (((4,6,5) :: (((2,6,6) :: (certificate_376_part_24_M))))))))))))))

noncomputable def certificate_376_part_26_M : ForbiddenMatrix := ((0,8,6) :: (((0,8,5) :: (((3,5,0) :: (((6,7,1) :: (((5,6,1) :: (((4,6,6) :: (((4,6,5) :: (((2,6,6) :: (certificate_376_part_24_M))))))))))))))))

noncomputable def certificate_376_part_27_M : ForbiddenMatrix := ((6,8,4) :: (((6,8,3) :: (((6,8,2) :: (((6,8,1) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,8,2) :: (certificate_376_part_26_M))))))))))))))))

noncomputable def certificate_376_part_28_M : ForbiddenMatrix := ((0,12,4) :: (((0,12,3) :: (((0,12,2) :: (((0,12,1) :: (((0,12,0) :: (((6,8,6) :: (((6,8,5) :: (certificate_376_part_27_M))))))))))))))

noncomputable def certificate_376_part_29_M : ForbiddenMatrix := ((4,12,1) :: (((4,12,0) :: (((4,8,0) :: (((4,6,1) :: (((4,6,0) :: (((2,12,0) :: (((1,12,0) :: (((0,12,5) :: (certificate_376_part_28_M))))))))))))))))

noncomputable def certificate_376_part_30_M : ForbiddenMatrix := ((6,12,4) :: (((6,12,3) :: (((6,12,2) :: (((6,12,1) :: (((6,12,0) :: (((4,12,4) :: (((4,12,3) :: (((4,12,2) :: (certificate_376_part_29_M))))))))))))))))

noncomputable def certificate_376_part_31_M : ForbiddenMatrix := ((3,8,2) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (((6,8,6) :: (((6,8,5) :: (certificate_376_part_27_M))))))))))))))))

noncomputable def certificate_376_part_32_M : ForbiddenMatrix := ((0,1,3) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (certificate_376_part_31_M))))))))))))))

noncomputable def certificate_376_part_33_M : ForbiddenMatrix := ((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (certificate_376_part_31_M))))))))))))))

noncomputable def certificate_376_part_34_M : ForbiddenMatrix := ((4,7,0) :: (((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (certificate_376_part_31_M))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_398_part_1_M : ForbiddenMatrix := ((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,1,1) :: (certificate_398_M))))))))))))))))

noncomputable def certificate_398_part_2_M : ForbiddenMatrix := ((0,4,6) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_398_part_1_M))))))))))))))))

noncomputable def certificate_398_part_3_M : ForbiddenMatrix := ((1,3,1) :: (((1,2,1) :: (((0,7,6) :: (((0,7,5) :: (((0,7,4) :: (((0,7,2) :: (((0,7,1) :: (((0,5,1) :: (certificate_398_part_2_M))))))))))))))))

noncomputable def certificate_398_part_4_M : ForbiddenMatrix := ((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (certificate_398_part_3_M))))))))))))))))

noncomputable def certificate_398_part_5_M : ForbiddenMatrix := ((1,7,6) :: (((1,7,5) :: (((1,7,4) :: (((1,7,2) :: (((1,7,1) :: (((1,5,1) :: (((1,4,6) :: (((1,4,5) :: (certificate_398_part_4_M))))))))))))))))

noncomputable def certificate_398_part_6_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (((2,7,1) :: (((2,3,1) :: (certificate_398_part_5_M))))))))))))))))

noncomputable def certificate_398_part_7_M : ForbiddenMatrix := ((4,5,1) :: (((3,8,1) :: (((3,7,6) :: (((3,7,5) :: (((3,7,4) :: (((3,7,3) :: (((3,7,2) :: (((3,7,1) :: (certificate_398_part_6_M))))))))))))))))

noncomputable def certificate_398_part_8_M : ForbiddenMatrix := ((0,1,2) :: (((5,7,1) :: (((4,7,6) :: (((4,7,5) :: (((4,7,4) :: (((4,7,3) :: (((4,7,2) :: (certificate_398_part_7_M))))))))))))))

noncomputable def certificate_398_part_9_M : ForbiddenMatrix := ((0,2,2) :: (((0,3,0) :: (((5,7,1) :: (((4,7,6) :: (((4,7,5) :: (((4,7,4) :: (((4,7,3) :: (((4,7,2) :: (certificate_398_part_7_M))))))))))))))))

noncomputable def certificate_398_part_10_M : ForbiddenMatrix := ((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (certificate_398_part_9_M))))))))))))))))

noncomputable def certificate_398_part_11_M : ForbiddenMatrix := ((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((1,2,2) :: (((0,6,1) :: (certificate_398_part_10_M))))))))))))))))

noncomputable def certificate_398_part_12_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((1,6,1) :: (((1,5,6) :: (((1,5,5) :: (certificate_398_part_11_M))))))))))))))))

noncomputable def certificate_398_part_13_M : ForbiddenMatrix := ((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((2,8,1) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (certificate_398_part_12_M))))))))))))))))

noncomputable def certificate_398_part_14_M : ForbiddenMatrix := ((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((0,1,2) :: (((5,6,1) :: (((3,5,6) :: (((3,5,5) :: (certificate_398_part_13_M))))))))))))))

noncomputable def certificate_398_part_15_M : ForbiddenMatrix := ((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (((0,8,1) :: (((0,4,0) :: (((5,6,1) :: (((3,5,6) :: (((3,5,5) :: (certificate_398_part_13_M))))))))))))))))

noncomputable def certificate_398_part_16_M : ForbiddenMatrix := ((4,8,1) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (((3,8,2) :: (((1,8,1) :: (((0,8,6) :: (((0,8,5) :: (certificate_398_part_15_M))))))))))))))))

noncomputable def certificate_398_part_17_M : ForbiddenMatrix := ((5,8,4) :: (((5,8,3) :: (((5,8,2) :: (((5,8,1) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (certificate_398_part_16_M))))))))))))))))

noncomputable def certificate_398_part_18_M : ForbiddenMatrix := ((7,8,6) :: (((7,8,5) :: (((7,8,4) :: (((7,8,3) :: (((7,8,2) :: (((7,8,1) :: (((6,7,1) :: (((5,8,5) :: (certificate_398_part_17_M))))))))))))))))

noncomputable def certificate_398_part_19_M : ForbiddenMatrix := ((3,5,1) :: (((3,5,0) :: (((2,5,0) :: (((1,5,0) :: (((1,3,0) :: (((0,7,3) :: (((0,5,0) :: (certificate_398_part_18_M))))))))))))))

noncomputable def certificate_398_part_20_M : ForbiddenMatrix := ((0,1,2) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,7,3) :: (((2,7,2) :: (((0,4,1) :: (certificate_398_part_18_M))))))))))))))

noncomputable def certificate_398_part_21_M : ForbiddenMatrix := ((3,6,1) :: (((2,6,1) :: (((1,7,3) :: (((1,4,1) :: (((1,2,3) :: (((0,7,3) :: (((0,2,3) :: (((0,1,3) :: (certificate_398_part_20_M))))))))))))))))

noncomputable def certificate_398_part_22_M : ForbiddenMatrix := ((1,8,2) :: (((0,5,0) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,7,3) :: (((2,7,2) :: (((0,4,1) :: (certificate_398_part_18_M))))))))))))))))

noncomputable def certificate_398_part_23_M : ForbiddenMatrix := ((2,8,5) :: (((2,8,4) :: (((2,8,3) :: (((2,8,2) :: (((1,8,6) :: (((1,8,5) :: (((1,8,4) :: (((1,8,3) :: (certificate_398_part_22_M))))))))))))))))

noncomputable def certificate_398_part_24_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((0,1,2) :: (((2,10,1) :: (((0,8,0) :: (((3,8,6) :: (((2,8,6) :: (certificate_398_part_23_M))))))))))))))

noncomputable def certificate_398_part_25_M : ForbiddenMatrix := ((0,1,3) :: (((0,1,2) :: (((0,9,0) :: (((2,10,1) :: (((0,8,0) :: (((3,8,6) :: (((2,8,6) :: (certificate_398_part_23_M))))))))))))))

noncomputable def certificate_398_part_26_M : ForbiddenMatrix := ((0,1,2) :: (((1,3,0) :: (((0,9,0) :: (((2,10,1) :: (((0,8,0) :: (((3,8,6) :: (((2,8,6) :: (certificate_398_part_23_M))))))))))))))

noncomputable def certificate_398_part_27_M : ForbiddenMatrix := ((1,4,0) :: (((1,3,0) :: (((0,9,0) :: (((2,10,1) :: (((0,8,0) :: (((3,8,6) :: (((2,8,6) :: (certificate_398_part_23_M))))))))))))))

noncomputable def certificate_398_part_28_M : ForbiddenMatrix := ((2,6,1) :: (((1,7,3) :: (((1,4,1) :: (((1,2,3) :: (((0,7,3) :: (((0,2,3) :: (((0,1,3) :: (((0,1,2) :: (certificate_398_part_27_M))))))))))))))))

noncomputable def certificate_398_part_29_M : ForbiddenMatrix := ((1,5,0) :: (((1,4,0) :: (((1,3,0) :: (((0,9,0) :: (((2,10,1) :: (((0,8,0) :: (((3,8,6) :: (((2,8,6) :: (certificate_398_part_23_M))))))))))))))))

noncomputable def certificate_398_part_30_M : ForbiddenMatrix := ((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,8,0) :: (((2,5,0) :: (((2,4,0) :: (((1,8,0) :: (certificate_398_part_29_M))))))))))))))))

noncomputable def certificate_398_part_31_M : ForbiddenMatrix := ((0,12,0) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,8,2) :: (((3,5,0) :: (((2,4,6) :: (certificate_398_part_30_M))))))))))))))

noncomputable def certificate_398_part_32_M : ForbiddenMatrix := ((3,12,1) :: (((2,12,0) :: (((1,12,0) :: (((0,12,5) :: (((0,12,4) :: (((0,12,3) :: (((0,12,2) :: (((0,12,1) :: (certificate_398_part_31_M))))))))))))))))

noncomputable def certificate_398_part_33_M : ForbiddenMatrix := ((4,12,3) :: (((4,12,2) :: (((4,12,1) :: (((4,12,0) :: (((4,8,0) :: (((4,7,0) :: (((4,6,0) :: (((3,12,2) :: (certificate_398_part_32_M))))))))))))))))

noncomputable def certificate_398_part_34_M : ForbiddenMatrix := ((3,5,1) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,8,2) :: (((3,5,0) :: (((2,4,6) :: (certificate_398_part_30_M))))))))))))))

noncomputable def certificate_398_part_35_M : ForbiddenMatrix := ((3,6,0) :: (((3,5,1) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,8,2) :: (((3,5,0) :: (((2,4,6) :: (certificate_398_part_30_M))))))))))))))))

noncomputable def certificate_398_part_36_M : ForbiddenMatrix := ((2,5,1) :: (((2,4,1) :: (((1,4,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((0,1,2) :: (certificate_398_part_35_M))))))))))))))

noncomputable def certificate_398_part_37_M : ForbiddenMatrix := ((2,4,1) :: (((1,4,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((0,1,2) :: (((3,7,0) :: (certificate_398_part_35_M))))))))))))))

noncomputable def certificate_398_part_38_M : ForbiddenMatrix := ((0,1,2) :: (((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,8,0) :: (((3,7,0) :: (certificate_398_part_35_M))))))))))))))

noncomputable def certificate_398_part_39_M : ForbiddenMatrix := ((4,7,0) :: (((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,8,0) :: (((3,7,0) :: (certificate_398_part_35_M))))))))))))))

noncomputable def certificate_398_part_40_M : ForbiddenMatrix := ((4,8,0) :: (((4,7,0) :: (((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,8,0) :: (((3,7,0) :: (certificate_398_part_35_M))))))))))))))))

noncomputable def certificate_398_part_41_M : ForbiddenMatrix := ((1,6,6) :: (((1,6,5) :: (((1,6,4) :: (((1,6,2) :: (((0,6,6) :: (((0,6,5) :: (((0,6,4) :: (((0,6,2) :: (certificate_398_part_40_M))))))))))))))))

noncomputable def certificate_398_part_42_M : ForbiddenMatrix := ((3,6,6) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((2,6,6) :: (((2,6,5) :: (((2,6,4) :: (certificate_398_part_41_M))))))))))))))

noncomputable def certificate_398_part_43_M : ForbiddenMatrix := ((2,6,1) :: (((1,6,3) :: (((1,4,1) :: (((1,2,3) :: (((0,6,3) :: (((0,2,3) :: (((0,1,3) :: (((0,1,2) :: (certificate_398_part_42_M))))))))))))))))

noncomputable def certificate_398_part_17 : FiniteCertificate := .forbid 5 8 5 (.system [[0],[1],[2,3,4,5,12,13,14,15,16,8,7],[6],[11]]) (.forbid 6 7 1 (.system [[0],[1],[2,3,4,5,6,12,7,8,9,10,11]]) (.forbid 7 8 1 (.system [[0],[1],[2,3,4,5,6],[7,12,8,9,10,11]]) (.forbid 7 8 2 (.system [[0],[1],[2,3,4,5,6],[7,12,13,8,9,10,11]]) (.forbid 7 8 3 (.system [[0],[1],[2],[6],[7,12,13,14,8,9,10,11]]) (.forbid 7 8 4 (.system [[0],[1],[2],[6],[7,12,13,14,15,8,9,10,11]]) (.forbid 7 8 5 (.system [[0],[1],[2],[6],[7,12,13,14,15,16,8,9,10,11]]) (.forbid 7 8 6 (.system [[0],[1],[2],[6],[7,12,13,14,15,16,17,8,9,10,11]]) (certificate_398_part_18))))))))

noncomputable def certificate_398_part_16 : FiniteCertificate := .forbid 5 7 2 (.system [[0],[1],[2,3,4,5,12,13,7,8,9,10,11],[6]]) (.forbid 5 7 3 (.system [[0],[1],[2,3,4,5,12,13,14,7],[6],[11]]) (.forbid 5 7 4 (.system [[0],[1],[2,3,4,5,12,13,14,15,7],[6],[11]]) (.forbid 5 7 5 (.system [[0],[1],[2,3,4,5,12,13,14,15,16,7],[6],[11]]) (.forbid 5 8 1 (.system [[0],[1],[2,3,4,5,12,8,9,10,11],[6],[7]]) (.forbid 5 8 2 (.system [[0],[1],[2,3,4,5,12,13,8,7],[6],[11]]) (.forbid 5 8 3 (.system [[0],[1],[2,3,4,5,12,13,14,8,7],[6],[11]]) (.forbid 5 8 4 (.system [[0],[1],[2,3,4,5,12,13,14,15,8,7],[6],[11]]) (certificate_398_part_17))))))))

noncomputable def certificate_398_part_15 : FiniteCertificate := .forbid 0 8 5 (.system [[0,12,13,14,15,16,8,7],[1],[2],[6],[11]]) (.forbid 0 8 6 (.system [[0,12,13,14,15,16,17,8,7],[1],[2],[6],[11]]) (.forbid 1 8 1 (.system [[0],[1,12,8,9,10,11],[2,3,4,5,6],[7]]) (.forbid 3 8 2 (.system [[0],[1],[2,3,12,13,8,9,10,11],[6],[7]]) (.forbid 3 8 3 (.system [[0],[1],[2,3,12,13,14,8,9,10,11],[6],[7]]) (.forbid 3 8 4 (.system [[0],[1],[2,3,12,13,14,15,8,7],[6],[11]]) (.forbid 3 8 5 (.system [[0],[1],[2,3,12,13,14,15,16,8,7],[6],[11]]) (.forbid 4 8 1 (.system [[0],[1],[2,3,4,12,8,9,10,11],[6],[7]]) (certificate_398_part_16))))))))

noncomputable def certificate_398_part_13 : FiniteCertificate := .forbid 3 5 5 (.system [[0],[1],[2,3,12,13,14,15,16,5,6],[7],[11]]) (.forbid 3 5 6 (.system [[0],[1],[2,3,12,13,14,15,16,17,5,6],[7],[11]]) (.forbid 5 6 1 (.system [[0],[1],[2,3,4,5,12,6],[7,8,9,10,11]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,3,2,6,7,8,9,10,11,1,13,12]) (.forbid 0 1 3 (.cycle [0,4,3,2,7,8,9,10,11,1,14,13,12]) (.forbid 0 2 3 (.cycle [0,4,5,6,7,8,9,10,11,2,14,13,12]) (.forbid 1 2 3 (.cycle [1,7,8,9,10,11,0,4,3,2,14,13,12]) (certificate_398_part_14))))) (.forbid 0 8 1 (.system [[0,12,8,9,10,11],[1],[2,3,4,5,6],[7]]) (.forbid 0 8 2 (.system [[0,12,13,8,9,10,11],[1],[2,3,4,5,6],[7]]) (.forbid 0 8 3 (.system [[0,12,13,14,8,7],[1],[2,3,4,5,6],[11]]) (.forbid 0 8 4 (.system [[0,12,13,14,15,8,7],[1],[2,3,4,5,6],[11]]) (certificate_398_part_15))))))))

noncomputable def certificate_398_part_12 : FiniteCertificate := .forbid 2 5 3 (.system [[0],[1],[2,12,13,14,5,6],[7,8,9,10,11]]) (.forbid 2 5 4 (.system [[0],[1],[2,12,13,14,15,5,6],[7,8,9,10,11]]) (.forbid 2 5 5 (.system [[0],[1],[2,12,13,14,15,16,5,6],[7],[11]]) (.forbid 2 5 6 (.system [[0],[1],[2,12,13,14,15,16,17,5,6],[7],[11]]) (.forbid 2 8 1 (.system [[0],[1],[6,5,4,3,2,12,8,9,10,11],[7]]) (.forbid 3 5 2 (.system [[0],[1],[2,3,12,13,5,6],[7,8,9,10,11]]) (.forbid 3 5 3 (.system [[0],[1],[2,3,12,13,14,5,6],[7,8,9,10,11]]) (.forbid 3 5 4 (.system [[0],[1],[2,3,12,13,14,15,5,6],[7],[11]]) (certificate_398_part_13))))))))

noncomputable def certificate_398_part_11 : FiniteCertificate := .forbid 1 5 5 (.system [[0],[1,12,13,14,15,16,5,4,3,2],[6],[7],[11]]) (.forbid 1 5 6 (.system [[0],[1,12,13,14,15,16,17,5,4,3,2],[6],[7],[11]]) (.forbid 1 6 1 (.system [[0],[1,12,6,5,4,3,2],[7,8,9,10,11]]) (.forbid 2 3 2 (.system [[0],[1],[2,12,13,3,4,5,6],[7,8,9,10,11]]) (.forbid 2 3 3 (.system [[0],[1],[2,12,13,14,3,4,5,6],[7],[11]]) (.forbid 2 3 4 (.system [[0],[1],[2,12,13,14,15,3,4,5,6],[7],[11]]) (.forbid 2 3 5 (.system [[0],[1],[2,12,13,14,15,16,3,4,5,6],[7],[11]]) (.forbid 2 3 6 (.system [[0],[1],[2,12,13,14,15,16,17,3,4,5,6],[7],[11]]) (certificate_398_part_12))))))))

noncomputable def certificate_398_part_10 : FiniteCertificate := .forbid 0 6 1 (.system [[0,12,6,5,4,3,2],[1],[7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3,4,5,6],[7,8,9,10,11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2,3,4,5,6],[7],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2,3,4,5,6],[7],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[6],[7],[11]]) (.forbid 1 5 2 (.system [[0],[1,12,13,5,4,3,2],[6],[7,8,9,10,11]]) (.forbid 1 5 3 (.system [[0],[1,12,13,14,5,4,3,2],[6],[7],[11]]) (.forbid 1 5 4 (.system [[0],[1,12,13,14,15,5,4,3,2],[6],[7],[11]]) (certificate_398_part_11))))))))

noncomputable def certificate_398_part_9 : FiniteCertificate := .forbid 0 2 4 (.system [[0,12,13,14,15,2,3,4,5,6],[1],[7],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2,3,4,5,6],[1],[7],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[6],[7],[11]]) (.forbid 0 5 2 (.system [[0,12,13,5,4,3,2],[1],[6],[7,8,9,10,11]]) (.forbid 0 5 3 (.system [[0,12,13,14,5,4,3,2],[1],[6],[7],[11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5,4,3,2],[1],[6],[7],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4,3,2],[1],[6],[7],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4,3,2],[1],[6],[7],[11]]) (certificate_398_part_10))))))))

noncomputable def certificate_398_part_7 : FiniteCertificate := .forbid 4 7 2 (.system [[0],[1],[2,3,4,12,13,7,8,9,10,11],[6]]) (.forbid 4 7 3 (.system [[0],[1],[2,3,4,12,13,14,7,8,9,10,11],[6]]) (.forbid 4 7 4 (.system [[0],[1],[2,3,4,12,13,14,15,7],[6],[11]]) (.forbid 4 7 5 (.system [[0],[1],[2,3,4,12,13,14,15,16,7],[6],[11]]) (.forbid 4 7 6 (.system [[0],[1],[2,3,4,12,13,14,15,16,17,7],[6],[11]]) (.forbid 5 7 1 (.system [[0],[1],[2,3,4,5,12,7,8,9,10,11],[6]]) (.forbid 0 3 0 (.forbid 0 1 2 (.cycle [0,3,4,5,6,7,8,9,10,11,1,13,12]) (certificate_398_part_8)) (.forbid 0 2 2 (.system [[0,12,13,2,3,4,5,6],[1],[7,8,9,10,11]]) (certificate_398_part_9))))))))

noncomputable def certificate_398_part_6 : FiniteCertificate := .forbid 3 7 1 (.system [[0],[1],[2],[6,5,4,3,12,7,8,9,10,11]]) (.forbid 3 7 2 (.system [[0],[1],[2],[6,5,4,3,12,13,7,8,9,10,11]]) (.forbid 3 7 3 (.system [[0],[1],[2,3,12,13,14,7,8,9,10,11],[6]]) (.forbid 3 7 4 (.system [[0],[1],[2,3,12,13,14,15,7,8,9,10,11],[6]]) (.forbid 3 7 5 (.system [[0],[1],[2,3,12,13,14,15,16,7],[6],[11]]) (.forbid 3 7 6 (.system [[0],[1],[2,3,12,13,14,15,16,17,7],[6],[11]]) (.forbid 3 8 1 (.system [[0],[1],[2],[6,5,4,3,12,8,9,10,11],[7]]) (.forbid 4 5 1 (.system [[0],[1],[2,3,4,12,5,6],[7,8,9,10,11]]) (certificate_398_part_7))))))))

noncomputable def certificate_398_part_5 : FiniteCertificate := .forbid 2 3 1 (.system [[0],[1],[2,12,3,4,5,6],[7,8,9,10,11]]) (.forbid 2 7 1 (.system [[0],[1],[6,5,4,3,2,12,7,8,9,10,11]]) (.forbid 3 4 1 (.system [[0],[1],[2,3,12,4,5,6],[7,8,9,10,11]]) (.forbid 3 4 2 (.system [[0],[1],[2,3,12,13,4,5,6],[7,8,9,10,11]]) (.forbid 3 4 3 (.system [[0],[1],[2,3,12,13,14,4,5,6],[7],[11]]) (.forbid 3 4 4 (.system [[0],[1],[2,3,12,13,14,15,4,5,6],[7],[11]]) (.forbid 3 4 5 (.system [[0],[1],[2,3,12,13,14,15,16,4,5,6],[7],[11]]) (.forbid 3 4 6 (.system [[0],[1],[2,3,12,13,14,15,16,17,4,5,6],[7],[11]]) (certificate_398_part_6))))))))

noncomputable def certificate_398_part_4 : FiniteCertificate := .forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4,3,2],[6],[7],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4,3,2],[6],[7],[11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,4,3,2],[6],[7,8,9,10,11]]) (.forbid 1 7 1 (.system [[0],[1,12,7,8,9,10,11],[2,3,4,5,6]]) (.forbid 1 7 2 (.system [[0],[1,12,13,7,8,9,10,11],[2,3,4,5,6]]) (.forbid 1 7 4 (.system [[0],[1,12,13,14,15,7],[2,3,4,5,6],[11]]) (.forbid 1 7 5 (.system [[0],[1,12,13,14,15,16,7],[2,3,4,5,6],[11]]) (.forbid 1 7 6 (.system [[0],[1,12,13,14,15,16,17,7],[2],[6],[11]]) (certificate_398_part_5))))))))

noncomputable def certificate_398_part_3 : FiniteCertificate := .forbid 1 3 2 (.system [[0],[1,12,13,3,4,5,6],[2],[7,8,9,10,11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3,2],[6],[7,8,9,10,11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3,2],[6],[7,8,9,10,11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3,2],[6],[7],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3,2],[6],[7],[11]]) (.forbid 1 4 2 (.system [[0],[1,12,13,4,3,2],[6],[7,8,9,10,11]]) (.forbid 1 4 3 (.system [[0],[1,12,13,14,4,3,2],[6],[7,8,9,10,11]]) (.forbid 1 4 4 (.system [[0],[1,12,13,14,15,4,3,2],[6],[7],[11]]) (certificate_398_part_4))))))))

noncomputable def certificate_398_part_2 : FiniteCertificate := .forbid 0 5 1 (.system [[0,12,5,4,3,2],[1],[6],[7,8,9,10,11]]) (.forbid 0 7 1 (.system [[0,12,7,8,9,10,11],[1],[2,3,4,5,6]]) (.forbid 0 7 2 (.system [[0,12,13,7,8,9,10,11],[1],[2,3,4,5,6]]) (.forbid 0 7 4 (.system [[0,12,13,14,15,7],[1],[2,3,4,5,6],[11]]) (.forbid 0 7 5 (.system [[0,12,13,14,15,16,7],[1],[2,3,4,5,6],[11]]) (.forbid 0 7 6 (.system [[0,12,13,14,15,16,17,7],[1],[2],[6],[11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3,4,5,6],[7,8,9,10,11]]) (.forbid 1 3 1 (.system [[0],[1,12,3,4,5,6],[2],[7,8,9,10,11]]) (certificate_398_part_3))))))))

noncomputable def certificate_398_part_1 : FiniteCertificate := .forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[1],[6],[7,8,9,10,11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[1],[6],[7],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[1],[6],[7],[11]]) (.forbid 0 4 2 (.system [[0,12,13,4,3,2],[1],[6],[7,8,9,10,11]]) (.forbid 0 4 3 (.system [[0,12,13,14,4,3,2],[1],[6],[7,8,9,10,11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4,3,2],[1],[6],[7],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4,3,2],[1],[6],[7],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4,3,2],[1],[6],[7],[11]]) (certificate_398_part_2))))))))

noncomputable def certificate_398 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2,3,4,5,6],[7,8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2,3,4,5,6],[7],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2,3,4,5,6],[7],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[6],[7],[11]]) (.forbid 0 2 1 (.system [[0,12,2,3,4,5,6],[1],[7,8,9,10,11]]) (.forbid 0 3 1 (.system [[0,12,3,4,5,6],[1],[2],[7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3,4,5,6],[1],[2],[7,8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[1],[6],[7,8,9,10,11]]) (certificate_398_part_1))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_490 : FiniteCertificate := .forbid 0 1 1 (.system [[0,11,1,2,3,4,5],[6,7,8,9,10]]) (.forbid 0 1 2 (.system [[0,11,12,1,2,3,4,5],[6],[8],[10]]) (.forbid 0 1 3 (.system [[0,11,12,13,1,2,3],[5],[6],[8],[10]]) (.forbid 0 1 4 (.system [[0,11,12,13,14,1],[3],[5],[6],[8],[10]]) (.forbid 0 1 5 (.system [[0,11,12,13,14,15,1],[3],[5],[6],[8],[10]]) (.forbid 0 1 6 (.system [[0,11,12,13,14,15,16,1],[3],[5],[6],[8],[10]]) (.forbid 0 2 1 (.system [[0,11,2,1],[3,4,5],[6,7,8],[10]]) (.forbid 0 2 2 (.system [[0,11,12,2,1],[3,4,5],[6],[8],[10]]) (.forbid 0 2 3 (.system [[0,11,12,13,2,1],[3],[5],[6],[8],[10]]) (.forbid 0 2 4 (.system [[0,11,12,13,14,2,1],[3],[5],[6],[8],[10]]) (.forbid 0 2 5 (.system [[0,11,12,13,14,15,2,1],[3],[5],[6],[8],[10]]) (.forbid 0 2 6 (.system [[0,11,12,13,14,15,16,2,1],[3],[5],[6],[8],[10]]) (.forbid 0 4 1 (.system [[0,11,4,3,2,1],[5],[6,7,8],[10]]) (.forbid 0 4 2 (.system [[0,11,12,4,3,2,1],[5],[6],[8],[10]]) (.forbid 0 4 3 (.system [[0,11,12,13,4,3],[1],[5],[6],[8],[10]]) (.forbid 0 4 4 (.system [[0,11,12,13,14,4,3],[1],[5],[6],[8],[10]]) (.forbid 0 4 5 (.system [[0,11,12,13,14,15,4,3],[1],[5],[6],[8],[10]]) (.forbid 0 4 6 (.system [[0,11,12,13,14,15,16,4,3],[1],[5],[6],[8],[10]]) (.forbid 0 5 1 (.system [[0,11,5,4,3,2,1],[6,7,8,9,10]]) (.forbid 0 6 1 (.system [[0,11,6,7,8,9,10],[1,2,3,4,5]]) (certificate_490_part_2))))))))))))))))))))

noncomputable def certificate_494_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,11,6,7,8],[2],[3,4,5],[10]]) (.forbid 1 6 2 (.system [[0,1,11,12,6],[2],[3,4,5],[8],[10]]) (.forbid 1 6 3 (.system [[0,1,11,12,13,6],[2],[3],[5],[8],[10]]) (.forbid 1 6 4 (.system [[0,1,11,12,13,14,6],[2],[3],[5],[8],[10]]) (.forbid 1 6 5 (.system [[0,1,11,12,13,14,15,6],[2],[3],[5],[8],[10]]) (.forbid 1 6 6 (.system [[0,1,11,12,13,14,15,16,6],[2],[3],[5],[8],[10]]) (.forbid 2 3 1 (.system [[0,1,2,11,3,4,5],[6,7,8,9,10]]) (.forbid 2 4 1 (.system [[0,1,2,11,4,3],[5],[6,7,8],[10]]) (.forbid 2 6 1 (.system [[0,1,2,11,6,7,8,9,10],[3,4,5]]) (.forbid 3 4 1 (.system [[0,1,2],[3,11,4,5],[6,7,8],[10]]) (.forbid 3 4 2 (.system [[0,1,2],[3,11,12,4,5],[6],[8],[10]]) (.forbid 3 4 3 (.system [[0],[2],[3,11,12,13,4,5],[6],[8],[10]]) (.forbid 3 4 4 (.system [[0],[2],[3,11,12,13,14,4,5],[6],[8],[10]]) (.forbid 3 4 5 (.system [[0],[2],[3,11,12,13,14,15,4,5],[6],[8],[10]]) (.forbid 3 4 6 (.system [[0],[2],[3,11,12,13,14,15,16,4,5],[6],[8],[10]]) (.forbid 3 6 1 (.system [[0,1,2],[5,4,3,11,6,7,8,9,10]]) (.forbid 3 6 2 (.system [[0,1,2],[5,4,3,11,12,6],[8],[10]]) (.forbid 3 6 3 (.system [[0,1,2],[3,11,12,13,6],[5],[8],[10]]) (.forbid 3 6 4 (.system [[0],[2],[3,11,12,13,14,6],[5],[8],[10]]) (.forbid 3 6 5 (.system [[0],[2],[3,11,12,13,14,15,6],[5],[8],[10]]) (certificate_494_part_0))))))))))))))))))))

noncomputable def certificate_494_part_2 : FiniteCertificate := .forbid 0 6 2 (.system [[2,1,0,11,12,6],[3,4,5],[8],[10]]) (.forbid 0 6 3 (.system [[2,1,0,11,12,13,6],[3],[5],[8],[10]]) (.forbid 0 6 4 (.system [[0,11,12,13,14,6],[2],[3],[5],[8],[10]]) (.forbid 0 6 5 (.system [[0,11,12,13,14,15,6],[2],[3],[5],[8],[10]]) (.forbid 0 6 6 (.system [[0,11,12,13,14,15,16,6],[2],[3],[5],[8],[10]]) (.forbid 0 7 1 (.system [[2,1,0,11,7,6],[3,4,5],[8],[10]]) (.forbid 1 2 1 (.system [[0,1,11,2],[3,4,5],[6,7,8],[10]]) (.forbid 1 3 1 (.system [[0,1,11,3,4,5],[2],[6,7,8],[10]]) (.forbid 1 3 2 (.system [[0,1,11,12,3,4,5],[2],[6],[8],[10]]) (.forbid 1 3 3 (.system [[0,1,11,12,13,3],[2],[5],[6],[8],[10]]) (.forbid 1 3 4 (.system [[0,1,11,12,13,14,3],[2],[5],[6],[8],[10]]) (.forbid 1 3 5 (.system [[0,1,11,12,13,14,15,3],[2],[5],[6],[8],[10]]) (.forbid 1 3 6 (.system [[0,1,11,12,13,14,15,16,3],[2],[5],[6],[8],[10]]) (.forbid 1 4 1 (.system [[0,1,11,4,3],[2],[5],[6,7,8],[10]]) (.forbid 1 4 2 (.system [[0,1,11,12,4,3],[2],[5],[6],[8],[10]]) (.forbid 1 4 3 (.system [[0,1,11,12,13,4,3],[2],[5],[6],[8],[10]]) (.forbid 1 4 4 (.system [[0,1,11,12,13,14,4,3],[2],[5],[6],[8],[10]]) (.forbid 1 4 5 (.system [[0,1,11,12,13,14,15,4,3],[2],[5],[6],[8],[10]]) (.forbid 1 4 6 (.system [[0,1,11,12,13,14,15,16,4,3],[2],[5],[6],[8],[10]]) (.forbid 1 5 1 (.system [[0,1,11,5,4,3],[2],[6,7,8],[10]]) (certificate_494_part_1))))))))))))))))))))

noncomputable def certificate_494 : FiniteCertificate := .forbid 0 1 1 (.system [[0,11,1,2],[3,4,5],[6,7,8],[10]]) (.forbid 0 1 2 (.system [[0,11,12,1,2],[3,4,5],[6],[8],[10]]) (.forbid 0 1 3 (.system [[0,11,12,13,1,2],[3],[5],[6],[8],[10]]) (.forbid 0 1 4 (.system [[0,11,12,13,14,1,2],[3],[5],[6],[8],[10]]) (.forbid 0 1 5 (.system [[0,11,12,13,14,15,1,2],[3],[5],[6],[8],[10]]) (.forbid 0 1 6 (.system [[0,11,12,13,14,15,16,1,2],[3],[5],[6],[8],[10]]) (.forbid 0 3 1 (.system [[2,1,0,11,3,4,5],[6,7,8,9,10]]) (.forbid 0 3 2 (.system [[2,1,0,11,12,3,4,5],[6],[8],[10]]) (.forbid 0 3 3 (.system [[2,1,0,11,12,13,3],[5],[6],[8],[10]]) (.forbid 0 3 4 (.system [[0,11,12,13,14,3],[2],[5],[6],[8],[10]]) (.forbid 0 3 5 (.system [[0,11,12,13,14,15,3],[2],[5],[6],[8],[10]]) (.forbid 0 3 6 (.system [[0,11,12,13,14,15,16,3],[2],[5],[6],[8],[10]]) (.forbid 0 4 1 (.system [[2,1,0,11,4,3],[5],[6,7,8],[10]]) (.forbid 0 4 2 (.system [[2,1,0,11,12,4,3],[5],[6],[8],[10]]) (.forbid 0 4 3 (.system [[0,11,12,13,4,3],[2],[5],[6],[8],[10]]) (.forbid 0 4 4 (.system [[0,11,12,13,14,4,3],[2],[5],[6],[8],[10]]) (.forbid 0 4 5 (.system [[0,11,12,13,14,15,4,3],[2],[5],[6],[8],[10]]) (.forbid 0 4 6 (.system [[0,11,12,13,14,15,16,4,3],[2],[5],[6],[8],[10]]) (.forbid 0 5 1 (.system [[2,1,0,11,5,4,3],[6,7,8,9,10]]) (.forbid 0 6 1 (.system [[2,1,0,11,6,7,8,9,10],[3,4,5]]) (certificate_494_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates017
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_532_part_1_M : ForbiddenMatrix := ((0,3,2) :: (((0,3,1) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_532_M))))))))))))))))

noncomputable def certificate_532_part_2_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,1) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((0,3,3) :: (certificate_532_part_1_M))))))))))))))))

noncomputable def certificate_532_part_3_M : ForbiddenMatrix := ((1,2,2) :: (((1,2,1) :: (((0,7,6) :: (((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,4,4) :: (((0,4,3) :: (certificate_532_part_2_M))))))))))))))))

noncomputable def certificate_532_part_4_M : ForbiddenMatrix := ((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,3) :: (certificate_532_part_3_M))))))))))))))))

noncomputable def certificate_532_part_5_M : ForbiddenMatrix := ((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (certificate_532_part_4_M))))))))))))))))

noncomputable def certificate_532_part_6_M : ForbiddenMatrix := ((3,4,2) :: (((3,4,1) :: (((2,7,3) :: (((2,5,2) :: (((2,5,1) :: (((2,4,1) :: (((2,3,1) :: (((1,7,6) :: (certificate_532_part_5_M))))))))))))))))

noncomputable def certificate_532_part_7_M : ForbiddenMatrix := ((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,7,4) :: (((3,7,3) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (certificate_532_part_6_M))))))))))))))))

noncomputable def certificate_532_part_8_M : ForbiddenMatrix := ((0,1,4) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((4,7,4) :: (((4,7,3) :: (certificate_532_part_7_M))))))))))))))

noncomputable def certificate_532_part_9_M : ForbiddenMatrix := ((1,7,2) :: (((1,7,1) :: (((1,3,4) :: (((0,7,2) :: (((0,7,1) :: (((0,3,4) :: (((0,1,6) :: (((0,1,5) :: (certificate_532_part_8_M))))))))))))))))

noncomputable def certificate_532_part_10_M : ForbiddenMatrix := ((0,6,0) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((4,7,4) :: (((4,7,3) :: (certificate_532_part_7_M))))))))))))))

noncomputable def certificate_532_part_11_M : ForbiddenMatrix := ((0,13,1) :: (((0,7,2) :: (((0,7,1) :: (((0,7,0) :: (((0,5,0) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_532_part_10_M))))))))))))))))

noncomputable def certificate_532_part_12_M : ForbiddenMatrix := ((1,7,2) :: (((1,7,1) :: (((1,7,0) :: (((1,5,0) :: (((0,13,5) :: (((0,13,4) :: (((0,13,3) :: (((0,13,2) :: (certificate_532_part_11_M))))))))))))))))

noncomputable def certificate_532_part_13_M : ForbiddenMatrix := ((2,7,0) :: (((2,5,0) :: (((1,13,5) :: (((1,13,4) :: (((1,13,3) :: (((1,13,2) :: (((1,13,1) :: (((1,13,0) :: (certificate_532_part_12_M))))))))))))))))

noncomputable def certificate_532_part_14_M : ForbiddenMatrix := ((5,11,0) :: (((5,7,1) :: (((5,7,0) :: (((4,13,0) :: (((3,13,0) :: (((3,7,0) :: (((3,5,0) :: (((2,13,0) :: (certificate_532_part_13_M))))))))))))))))

noncomputable def certificate_532_part_15_M : ForbiddenMatrix := ((7,13,2) :: (((7,13,1) :: (((7,13,0) :: (((5,13,4) :: (((5,13,3) :: (((5,13,2) :: (((5,13,1) :: (((5,13,0) :: (certificate_532_part_14_M))))))))))))))))

noncomputable def certificate_532_part_16_M : ForbiddenMatrix := ((0,6,1) :: (((0,6,0) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((4,7,4) :: (((4,7,3) :: (certificate_532_part_7_M))))))))))))))))

noncomputable def certificate_532_part_17_M : ForbiddenMatrix := ((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,3,3) :: (((2,3,2) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (certificate_532_part_16_M))))))))))))))))

noncomputable def certificate_532_part_18_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((3,4,4) :: (((3,4,3) :: (certificate_532_part_17_M))))))))))))))

noncomputable def certificate_532_part_19_M : ForbiddenMatrix := ((1,2,5) :: (((1,2,4) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (certificate_532_part_18_M))))))))))))))))

noncomputable def certificate_532_part_20_M : ForbiddenMatrix := ((2,3,4) :: (((1,6,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (certificate_532_part_19_M))))))))))))))))

noncomputable def certificate_532_part_21_M : ForbiddenMatrix := ((3,6,1) :: (((3,4,6) :: (((3,4,5) :: (((2,6,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (certificate_532_part_20_M))))))))))))))))

noncomputable def certificate_532_part_22_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,7,0) :: (((3,4,4) :: (((3,4,3) :: (certificate_532_part_17_M))))))))))))))

noncomputable def certificate_532_part_23_M : ForbiddenMatrix := ((0,7,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (certificate_532_part_22_M))))))))))))))))

noncomputable def certificate_532_part_24_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (certificate_532_part_23_M))))))))))))))))

noncomputable def certificate_532_part_25_M : ForbiddenMatrix := ((3,4,5) :: (((2,7,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,7,1) :: (certificate_532_part_24_M))))))))))))))))

noncomputable def certificate_532_part_26_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,8,0) :: (((0,7,0) :: (((3,4,4) :: (((3,4,3) :: (certificate_532_part_17_M))))))))))))))

noncomputable def certificate_532_part_27_M : ForbiddenMatrix := ((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (certificate_532_part_26_M))))))))))))))))

noncomputable def certificate_532_part_28_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (certificate_532_part_27_M))))))))))))))))

noncomputable def certificate_532_part_29_M : ForbiddenMatrix := ((2,8,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,4,6) :: (certificate_532_part_28_M))))))))))))))))

noncomputable def certificate_532_part_30_M : ForbiddenMatrix := ((0,11,3) :: (((0,11,2) :: (((0,11,1) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,4) :: (((3,4,3) :: (certificate_532_part_17_M))))))))))))))))

noncomputable def certificate_532_part_31_M : ForbiddenMatrix := ((2,5,3) :: (((1,11,5) :: (((1,11,4) :: (((1,11,3) :: (((1,11,2) :: (((1,11,1) :: (((0,11,5) :: (((0,11,4) :: (certificate_532_part_30_M))))))))))))))))

noncomputable def certificate_532_part_32_M : ForbiddenMatrix := ((4,5,4) :: (((3,11,3) :: (((3,11,2) :: (((3,11,1) :: (((3,5,4) :: (((2,11,2) :: (((2,11,1) :: (certificate_532_part_31_M))))))))))))))

noncomputable def certificate_532_part_33_M : ForbiddenMatrix := ((4,11,1) :: (((1,5,6) :: (((1,3,4) :: (((0,5,6) :: (((0,3,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_532_part_32_M))))))))))))))))

noncomputable def certificate_532_part_34_M : ForbiddenMatrix := ((0,10,0) :: (((4,5,4) :: (((3,11,3) :: (((3,11,2) :: (((3,11,1) :: (((3,5,4) :: (((2,11,2) :: (((2,11,1) :: (certificate_532_part_31_M))))))))))))))))

noncomputable def certificate_532_part_35_M : ForbiddenMatrix := ((1,3,4) :: (((0,7,2) :: (((0,7,1) :: (((0,3,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_532_part_34_M))))))))))))))

noncomputable def certificate_532_part_36_M : ForbiddenMatrix := ((4,7,2) :: (((4,7,1) :: (((3,7,2) :: (((3,7,1) :: (((2,7,2) :: (((2,7,1) :: (((1,7,2) :: (((1,7,1) :: (certificate_532_part_35_M))))))))))))))))

noncomputable def certificate_532_part_37_M : ForbiddenMatrix := ((0,7,2) :: (((0,7,1) :: (((0,5,0) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((1,6,0) :: (certificate_532_part_34_M))))))))))))))

noncomputable def certificate_532_part_38_M : ForbiddenMatrix := ((1,7,0) :: (((1,5,0) :: (((0,13,5) :: (((0,13,4) :: (((0,13,3) :: (((0,13,2) :: (((0,13,1) :: (((0,13,0) :: (certificate_532_part_37_M))))))))))))))))

noncomputable def certificate_532_part_39_M : ForbiddenMatrix := ((2,5,0) :: (((1,13,5) :: (((1,13,4) :: (((1,13,3) :: (((1,13,2) :: (((1,13,1) :: (((1,7,2) :: (((1,7,1) :: (certificate_532_part_38_M))))))))))))))))

noncomputable def certificate_532_part_40_M : ForbiddenMatrix := ((5,7,1) :: (((5,7,0) :: (((4,13,0) :: (((3,13,0) :: (((3,7,0) :: (((3,5,0) :: (((2,13,0) :: (((2,7,0) :: (certificate_532_part_39_M))))))))))))))))

noncomputable def certificate_532_part_41_M : ForbiddenMatrix := ((7,13,1) :: (((7,13,0) :: (((5,13,4) :: (((5,13,3) :: (((5,13,2) :: (((5,13,1) :: (((5,13,0) :: (((5,11,0) :: (certificate_532_part_40_M))))))))))))))))

noncomputable def certificate_532_part_42_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,6,0) :: (certificate_532_part_34_M))))))))))))))

noncomputable def certificate_532_part_43_M : ForbiddenMatrix := ((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (certificate_532_part_42_M))))))))))))))))

noncomputable def certificate_532_part_44_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (certificate_532_part_43_M))))))))))))))))

noncomputable def certificate_532_part_45_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,6,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (certificate_532_part_44_M))))))))))))))))

noncomputable def certificate_532_part_46_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((1,7,0) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,6,0) :: (certificate_532_part_34_M))))))))))))))

noncomputable def certificate_532_part_47_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (certificate_532_part_46_M))))))))))))))))

noncomputable def certificate_532_part_48_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,4,6) :: (certificate_532_part_47_M))))))))))))))))

noncomputable def certificate_532_part_49_M : ForbiddenMatrix := ((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,7,1) :: (((1,4,6) :: (((1,4,5) :: (certificate_532_part_48_M))))))))))))))))

noncomputable def certificate_532_part_50_M : ForbiddenMatrix := ((0,1,4) :: (((1,8,0) :: (((1,7,0) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,6,0) :: (certificate_532_part_34_M))))))))))))))

noncomputable def certificate_532_part_51_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (certificate_532_part_50_M))))))))))))))))

noncomputable def certificate_532_part_52_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (certificate_532_part_51_M))))))))))))))))

noncomputable def certificate_532_part_53_M : ForbiddenMatrix := ((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (certificate_532_part_52_M))))))))))))))))

noncomputable def certificate_532_part_54_M : ForbiddenMatrix := ((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,6,0) :: (certificate_532_part_34_M))))))))))))))

noncomputable def certificate_532_part_55_M : ForbiddenMatrix := ((4,11,1) :: (((1,5,6) :: (((1,3,4) :: (((0,5,6) :: (((0,3,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_532_part_54_M))))))))))))))))

noncomputable def certificate_532_part_56_M : ForbiddenMatrix := ((1,10,0) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,6,0) :: (certificate_532_part_34_M))))))))))))))))

noncomputable def certificate_532_part_57_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,5,5) :: (((2,5,4) :: (certificate_532_part_56_M))))))))))))))

noncomputable def certificate_532_part_58_M : ForbiddenMatrix := ((2,7,1) :: (((2,3,4) :: (((1,7,2) :: (((1,7,1) :: (((0,7,2) :: (((0,7,1) :: (((0,3,4) :: (((0,2,6) :: (certificate_532_part_57_M))))))))))))))))

noncomputable def certificate_532_part_59_M : ForbiddenMatrix := ((0,2,4) :: (((2,6,0) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,5,5) :: (((2,5,4) :: (certificate_532_part_56_M))))))))))))))

noncomputable def certificate_532_part_60_M : ForbiddenMatrix := ((0,13,2) :: (((0,13,1) :: (((0,13,0) :: (((0,7,2) :: (((0,7,1) :: (((0,5,0) :: (((0,2,6) :: (((0,2,5) :: (certificate_532_part_59_M))))))))))))))))

noncomputable def certificate_532_part_61_M : ForbiddenMatrix := ((2,7,1) :: (((2,7,0) :: (((2,5,0) :: (((1,13,0) :: (((1,5,0) :: (((0,13,5) :: (((0,13,4) :: (((0,13,3) :: (certificate_532_part_60_M))))))))))))))))

noncomputable def certificate_532_part_62_M : ForbiddenMatrix := ((3,7,0) :: (((3,5,0) :: (((2,13,5) :: (((2,13,4) :: (((2,13,3) :: (((2,13,2) :: (((2,13,1) :: (((2,7,2) :: (certificate_532_part_61_M))))))))))))))))

noncomputable def certificate_532_part_63_M : ForbiddenMatrix := ((5,13,2) :: (((5,13,1) :: (((5,13,0) :: (((5,11,0) :: (((5,7,1) :: (((5,7,0) :: (((4,13,0) :: (((3,13,0) :: (certificate_532_part_62_M))))))))))))))))

noncomputable def certificate_532_part_64_M : ForbiddenMatrix := ((2,6,2) :: (((2,6,1) :: (((2,6,0) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,5,5) :: (((2,5,4) :: (certificate_532_part_56_M))))))))))))))))

noncomputable def certificate_532_part_65_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((2,6,3) :: (certificate_532_part_64_M))))))))))))))

noncomputable def certificate_532_part_66_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_532_part_65_M))))))))))))))))

noncomputable def certificate_532_part_67_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (certificate_532_part_66_M))))))))))))))))

noncomputable def certificate_532_part_65 : FiniteCertificate := .forbid 0 3 4 (.cycle [0,1,2,7,8,9,10,11,12,3,16,15,14,13]) (.forbid 0 3 5 (.cycle [0,1,2,7,6,5,4,12,3,17,16,15,14,13]) (.forbid 0 3 6 (.cycle [0,1,2,7,6,5,4,3,18,17,16,15,14,13]) (.forbid 0 4 5 (.cycle [0,1,3,12,2,7,6,5,4,17,16,15,14,13]) (.forbid 0 4 6 (.cycle [0,1,3,2,7,6,5,4,18,17,16,15,14,13]) (.forbid 1 2 4 (.cycle [1,0,3,12,11,10,9,8,7,2,16,15,14,13]) (.forbid 1 2 5 (.cycle [1,0,3,12,4,5,6,7,2,17,16,15,14,13]) (.forbid 1 2 6 (.cycle [1,0,3,4,5,6,7,2,18,17,16,15,14,13]) (certificate_532_part_66))))))))

noncomputable def certificate_532_part_68_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((2,7,0) :: (((2,6,3) :: (certificate_532_part_64_M))))))))))))))

noncomputable def certificate_532_part_69_M : ForbiddenMatrix := ((1,2,4) :: (((0,7,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (certificate_532_part_68_M))))))))))))))))

noncomputable def certificate_532_part_70_M : ForbiddenMatrix := ((1,7,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (certificate_532_part_69_M))))))))))))))))

noncomputable def certificate_532_part_71_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (certificate_532_part_70_M))))))))))))))))

noncomputable def certificate_532_part_72_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((2,8,0) :: (((2,7,0) :: (((2,6,3) :: (certificate_532_part_64_M))))))))))))))

noncomputable def certificate_532_part_73_M : ForbiddenMatrix := ((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (certificate_532_part_72_M))))))))))))))))

noncomputable def certificate_532_part_74_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (certificate_532_part_73_M))))))))))))))))

noncomputable def certificate_532_part_75_M : ForbiddenMatrix := ((3,4,5) :: (((2,8,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,8,1) :: (certificate_532_part_74_M))))))))))))))))

noncomputable def certificate_532_part_76_M : ForbiddenMatrix := ((2,11,5) :: (((2,11,4) :: (((2,11,3) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,3) :: (certificate_532_part_64_M))))))))))))))

noncomputable def certificate_532_part_77_M : ForbiddenMatrix := ((4,11,1) :: (((2,5,6) :: (((2,3,4) :: (((0,5,6) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (certificate_532_part_76_M))))))))))))))))

noncomputable def certificate_532_part_78_M : ForbiddenMatrix := ((2,10,0) :: (((2,11,5) :: (((2,11,4) :: (((2,11,3) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,3) :: (certificate_532_part_64_M))))))))))))))))

noncomputable def certificate_532_part_79_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,2,4) :: (((3,7,6) :: (((3,7,5) :: (((3,5,5) :: (certificate_532_part_78_M))))))))))))))

noncomputable def certificate_532_part_80_M : ForbiddenMatrix := ((3,7,1) :: (((2,7,2) :: (((2,7,1) :: (((2,3,4) :: (((1,7,2) :: (((1,7,1) :: (((0,7,2) :: (((0,7,1) :: (certificate_532_part_79_M))))))))))))))))

noncomputable def certificate_532_part_81_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((3,6,0) :: (((3,7,6) :: (((3,7,5) :: (((3,5,5) :: (certificate_532_part_78_M))))))))))))))

noncomputable def certificate_532_part_82_M : ForbiddenMatrix := ((0,13,4) :: (((0,13,3) :: (((0,13,2) :: (((0,13,1) :: (((0,13,0) :: (((0,7,2) :: (((0,7,1) :: (((0,5,0) :: (certificate_532_part_81_M))))))))))))))))

noncomputable def certificate_532_part_83_M : ForbiddenMatrix := ((3,7,1) :: (((3,7,0) :: (((3,5,0) :: (((2,13,0) :: (((2,5,0) :: (((1,13,0) :: (((1,5,0) :: (((0,13,5) :: (certificate_532_part_82_M))))))))))))))))

noncomputable def certificate_532_part_84_M : ForbiddenMatrix := ((5,7,0) :: (((4,13,0) :: (((3,13,5) :: (((3,13,4) :: (((3,13,3) :: (((3,13,2) :: (((3,13,1) :: (((3,7,2) :: (certificate_532_part_83_M))))))))))))))))

noncomputable def certificate_532_part_85_M : ForbiddenMatrix := ((7,13,0) :: (((5,13,4) :: (((5,13,3) :: (((5,13,2) :: (((5,13,1) :: (((5,13,0) :: (((5,11,0) :: (((5,7,1) :: (certificate_532_part_84_M))))))))))))))))

noncomputable def certificate_532_part_86_M : ForbiddenMatrix := ((3,6,3) :: (((3,6,2) :: (((3,6,1) :: (((3,6,0) :: (((3,7,6) :: (((3,7,5) :: (((3,5,5) :: (certificate_532_part_78_M))))))))))))))

noncomputable def certificate_532_part_87_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_532_part_86_M))))))))))))))))

noncomputable def certificate_532_part_88_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (certificate_532_part_87_M))))))))))))))))

noncomputable def certificate_532_part_89_M : ForbiddenMatrix := ((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (certificate_532_part_88_M))))))))))))))))

noncomputable def certificate_532_part_90_M : ForbiddenMatrix := ((3,7,0) :: (((3,6,3) :: (((3,6,2) :: (((3,6,1) :: (((3,6,0) :: (((3,7,6) :: (((3,7,5) :: (((3,5,5) :: (certificate_532_part_78_M))))))))))))))))

noncomputable def certificate_532_part_91_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (certificate_532_part_90_M))))))))))))))

noncomputable def certificate_532_part_92_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,7,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (certificate_532_part_91_M))))))))))))))))

noncomputable def certificate_532_part_93_M : ForbiddenMatrix := ((2,3,5) :: (((2,3,4) :: (((1,7,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (certificate_532_part_92_M))))))))))))))))

noncomputable def certificate_532_part_94_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((3,8,0) :: (certificate_532_part_90_M))))))))))))))

noncomputable def certificate_532_part_95_M : ForbiddenMatrix := ((1,2,5) :: (((1,2,4) :: (((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_532_part_94_M))))))))))))))))

noncomputable def certificate_532_part_96_M : ForbiddenMatrix := ((2,3,4) :: (((1,8,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,2,6) :: (certificate_532_part_95_M))))))))))))))))

noncomputable def certificate_532_part_97_M : ForbiddenMatrix := ((3,8,1) :: (((3,4,6) :: (((3,4,5) :: (((2,8,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (certificate_532_part_96_M))))))))))))))))

noncomputable def certificate_532_part_98_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,2,4) :: (((3,11,5) :: (((3,11,4) :: (((3,9,0) :: (((3,8,0) :: (certificate_532_part_90_M))))))))))))))

noncomputable def certificate_532_part_99_M : ForbiddenMatrix := ((5,11,1) :: (((4,11,3) :: (((4,11,2) :: (((4,11,1) :: (((3,5,6) :: (((2,3,4) :: (((0,5,6) :: (((0,3,6) :: (certificate_532_part_98_M))))))))))))))))

noncomputable def certificate_532_part_100_M : ForbiddenMatrix := ((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (((3,10,0) :: (((3,11,5) :: (((3,11,4) :: (((3,9,0) :: (((3,8,0) :: (certificate_532_part_90_M))))))))))))))))

noncomputable def certificate_532_part_101_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,4) :: (((0,1,5) :: (((0,1,4) :: (((4,5,5) :: (((5,6,5) :: (((5,6,4) :: (certificate_532_part_100_M))))))))))))))

noncomputable def certificate_532_part_102_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,4) :: (((1,2,4) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,5) :: (((0,3,4) :: (certificate_532_part_101_M))))))))))))))))

noncomputable def certificate_532_part_64 : FiniteCertificate := .forbid 2 6 3 (.system [[0],[1],[2,13,14,15,6,7,8,9,10,11,12],[3],[4]]) (.forbid 2 7 0 (.forbid 0 1 4 (.cycle [0,2,7,8,9,10,11,12,3,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,2,7,6,5,4,3,12,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,2,7,6,5,4,3,1,18,17,16,15,14,13]) (.forbid 0 2 4 (.cycle [0,1,3,12,11,10,9,8,7,2,16,15,14,13]) (.forbid 0 2 5 (.cycle [0,1,3,12,4,5,6,7,2,17,16,15,14,13]) (.forbid 0 2 6 (.cycle [0,1,3,4,5,6,7,2,18,17,16,15,14,13]) (certificate_532_part_65))))))) (.forbid 2 8 0 (.forbid 0 1 4 (.cycle [0,2,8,7,6,5,4,3,12,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,2,8,7,6,5,4,3,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,2,8,7,6,5,4,1,18,17,16,15,14,13]) (.forbid 0 2 4 (.cycle [0,1,3,4,12,11,10,9,8,2,16,15,14,13]) (.forbid 0 2 5 (.cycle [0,1,3,4,5,6,7,8,2,17,16,15,14,13]) (certificate_532_part_68)))))) (.forbid 2 9 0 (.forbid 0 1 4 (.cycle [0,2,9,8,7,6,5,4,3,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,2,9,8,7,6,5,4,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,2,9,10,11,12,3,1,18,17,16,15,14,13]) (.forbid 0 2 4 (.cycle [0,1,3,4,5,6,7,8,9,2,16,15,14,13]) (certificate_532_part_72))))) (.forbid 2 11 3 (.system [[0],[1],[2,13,14,15,11,10,9,8,7,6,5,4],[3],[12]]) (.forbid 2 11 4 (.system [[0],[1],[2,13,14,15,16,11,10,9,8,7,6,5,4],[3],[12]]) (.forbid 2 11 5 (.system [[0],[1],[2,13,14,15,16,17,11,10,9,8,7,6,5,4],[3],[12]]) (.forbid 2 10 0 (certificate_532_part_76) (certificate_532_part_78))))))))

noncomputable def certificate_532_part_56 : FiniteCertificate := .forbid 2 5 4 (.system [[0],[1],[2,13,14,15,16,5,6,7,8,9,10,11,12],[3],[4]]) (.forbid 2 5 5 (.system [[0],[1],[2,13,14,15,16,17,5,6,7,8,9,10,11,12],[3],[4]]) (.forbid 2 7 4 (.system [[0],[1],[2,13,14,15,16,7,8,9,10,11,12],[3],[4]]) (.forbid 2 7 5 (.system [[0],[1],[2,13,14,15,16,17,7,6,5,4],[3],[12]]) (.forbid 2 7 6 (.system [[0],[1],[2,13,14,15,16,17,18,7,6,5,4],[3],[12]]) (.forbid 2 6 0 (.forbid 0 2 4 (.cycle [0,1,12,11,10,9,8,7,6,2,16,15,14,13]) (.forbid 0 2 5 (.cycle [0,12,11,10,9,8,7,6,2,17,16,15,14,13]) (certificate_532_part_57))) (.forbid 2 6 1 (.forbid 0 2 4 (.cycle [0,12,11,10,9,8,7,6,13,2,17,16,15,14]) (certificate_532_part_59)) (.forbid 2 6 2 (.system [[0],[1],[2,13,14,6,7,8,9,10,11,12],[3],[4]]) (certificate_532_part_64))))))))

noncomputable def certificate_532_part_34 : FiniteCertificate := .forbid 1 6 0 (.forbid 0 1 4 (.cycle [0,2,12,11,10,9,8,7,6,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,12,11,10,9,8,7,6,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,2,3,12,4,5,6,1,18,17,16,15,14,13]) (.forbid 0 3 4 (.cycle [0,1,6,7,8,9,10,11,12,3,16,15,14,13]) (.forbid 0 7 1 (.cycle [0,1,6,5,4,2,3,12,11,10,9,8,7,13]) (.forbid 0 7 2 (.cycle [0,1,6,5,4,2,12,11,10,9,8,7,14,13]) (.forbid 1 3 4 (.cycle [1,6,7,8,9,10,11,12,0,3,16,15,14,13]) (certificate_532_part_35)))))))) (.forbid 1 6 1 (.forbid 0 1 4 (.cycle [0,12,11,10,9,8,7,6,13,1,17,16,15,14]) (.forbid 0 1 5 (.cycle [0,2,3,12,4,5,6,13,1,18,17,16,15,14]) (.forbid 0 1 6 (.cycle [0,2,3,4,5,6,13,1,19,18,17,16,15,14]) (.forbid 0 5 0 (.cycle [0,1,13,6,7,8,9,10,11,12,2,3,4,5]) (.forbid 0 7 1 (.cycle [0,1,13,6,5,4,2,12,11,10,9,8,7,14]) (.forbid 0 7 2 (.cycle [0,1,13,6,5,4,12,11,10,9,8,7,15,14]) (certificate_532_part_37))))))) (.forbid 1 6 2 (.system [[0],[1,13,14,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 6 3 (.system [[0],[1,13,14,15,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 7 0 (.forbid 0 1 4 (.cycle [0,2,3,12,11,10,9,8,7,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,2,3,12,4,5,6,7,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,2,3,4,5,6,7,1,18,17,16,15,14,13]) (certificate_532_part_42)))) (.forbid 1 8 0 (.forbid 0 1 4 (.cycle [0,2,3,4,12,11,10,9,8,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,2,3,4,5,6,7,8,1,17,16,15,14,13]) (certificate_532_part_46))) (.forbid 1 9 0 (.forbid 0 1 4 (.cycle [0,2,3,4,5,6,7,8,9,1,16,15,14,13]) (certificate_532_part_50)) (.forbid 1 10 0 (certificate_532_part_54) (certificate_532_part_56))))))))

noncomputable def certificate_532_part_31 : FiniteCertificate := .forbid 2 11 1 (.system [[0],[1],[2,13,11,10,9,8,7,6,5,4],[3],[12]]) (.forbid 2 11 2 (.system [[0],[1],[2,13,14,11,10,9,8,7,6,5,4],[3],[12]]) (.forbid 3 5 4 (.system [[0],[1],[2],[3,13,14,15,16,5,6,7,8,9,10,11,12],[4]]) (.forbid 3 11 1 (.system [[0],[1],[2],[3,13,11,10,9,8,7,6,5,4],[12]]) (.forbid 3 11 2 (.system [[0],[1],[2],[3,13,14,11,10,9,8,7,6,5,4],[12]]) (.forbid 3 11 3 (.system [[0],[1],[2],[3,13,14,15,11,10,9,8,7,6,5,4],[12]]) (.forbid 4 5 4 (.system [[0],[1],[2],[3],[4,13,14,15,16,5,6,7,8,9,10,11,12]]) (.forbid 0 10 0 (certificate_532_part_32) (certificate_532_part_34))))))))

noncomputable def certificate_532_part_30 : FiniteCertificate := .forbid 0 11 4 (.system [[0,13,14,15,16,11,10,9,8,7,6,5,4],[1],[2],[3],[12]]) (.forbid 0 11 5 (.system [[0,13,14,15,16,17,11,10,9,8,7,6,5,4],[1],[2],[3],[12]]) (.forbid 1 11 1 (.system [[0],[1,13,11,10,9,8,7,6,5,4],[2],[3],[12]]) (.forbid 1 11 2 (.system [[0],[1,13,14,11,10,9,8,7,6,5,4],[2],[3],[12]]) (.forbid 1 11 3 (.system [[0],[1,13,14,15,11,10,9,8,7,6,5,4],[2],[3],[12]]) (.forbid 1 11 4 (.system [[0],[1,13,14,15,16,11,10,9,8,7,6,5,4],[2],[3],[12]]) (.forbid 1 11 5 (.system [[0],[1,13,14,15,16,17,11,10,9,8,7,6,5,4],[2],[3],[12]]) (.forbid 2 5 3 (.system [[0],[1],[2,13,14,15,5,6,7,8,9,10,11,12],[3],[4]]) (certificate_532_part_31))))))))

noncomputable def certificate_532_part_17 : FiniteCertificate := .forbid 3 4 3 (.system [[0],[1],[2],[3,13,14,15,4,5,6,7,8,9,10,11,12]]) (.forbid 3 4 4 (.system [[0],[1],[2],[3,13,14,15,16,4,5,6,7,8,9,10,11,12]]) (.forbid 0 7 0 (.forbid 0 1 4 (.cycle [0,7,8,9,10,11,12,2,3,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,7,6,5,4,2,3,12,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,7,6,5,4,2,3,1,18,17,16,15,14,13]) (.forbid 0 2 4 (.cycle [0,7,8,9,10,11,12,1,3,2,16,15,14,13]) (.forbid 0 2 5 (.cycle [0,7,6,5,4,1,3,12,2,17,16,15,14,13]) (certificate_532_part_18)))))) (.forbid 0 8 0 (.forbid 0 1 4 (.cycle [0,8,7,6,5,4,2,3,12,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,8,7,6,5,4,2,3,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,8,7,6,5,4,2,1,18,17,16,15,14,13]) (.forbid 0 2 4 (.cycle [0,8,7,6,5,4,1,3,12,2,16,15,14,13]) (certificate_532_part_22))))) (.forbid 0 9 0 (.forbid 0 1 4 (.cycle [0,9,8,7,6,5,4,2,3,1,16,15,14,13]) (.forbid 0 1 5 (.cycle [0,9,8,7,6,5,4,2,1,17,16,15,14,13]) (.forbid 0 1 6 (.cycle [0,9,8,7,6,5,4,1,18,17,16,15,14,13]) (certificate_532_part_26)))) (.forbid 0 11 1 (.system [[0,13,11,10,9,8,7,6,5,4],[1],[2],[3],[12]]) (.forbid 0 11 2 (.system [[0,13,14,11,10,9,8,7,6,5,4],[1],[2],[3],[12]]) (.forbid 0 11 3 (.system [[0,13,14,15,11,10,9,8,7,6,5,4],[1],[2],[3],[12]]) (certificate_532_part_30))))))))

noncomputable def certificate_532_part_16 : FiniteCertificate := .forbid 0 6 2 (.system [[0,13,14,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 6 3 (.system [[0,13,14,15,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 6 4 (.system [[0,13,14,15,16,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 2 3 2 (.system [[0],[1],[2,13,14,3],[4,5,6,7,8,9,10,11,12]]) (.forbid 2 3 3 (.system [[0],[1],[2,13,14,15,3],[4,5,6,7,8,9,10,11,12]]) (.forbid 2 4 2 (.system [[0],[1],[2,13,14,4,5,6,7,8,9,10,11,12],[3]]) (.forbid 2 4 3 (.system [[0],[1],[2,13,14,15,4,5,6,7,8,9,10,11,12],[3]]) (.forbid 2 4 4 (.system [[0],[1],[2,13,14,15,16,4,5,6,7,8,9,10,11,12],[3]]) (certificate_532_part_17))))))))

noncomputable def certificate_532_part_7 : FiniteCertificate := .forbid 4 7 3 (.system [[0],[1],[2],[3],[4,13,14,15,7,8,9,10,11,12]]) (.forbid 4 7 4 (.system [[0],[1],[2],[3],[4,13,14,15,16,7,8,9,10,11,12]]) (.forbid 5 7 2 (.system [[0],[1],[2],[3],[4,5,13,14,7,8,9,10,11,12]]) (.forbid 5 7 3 (.system [[0],[1],[2],[3],[4,5,13,14,15,7,8,9,10,11,12]]) (.forbid 5 7 4 (.system [[0],[1],[2],[3],[4,5,13,14,15,16,7,8,9,10,11,12]]) (.forbid 5 7 5 (.system [[0],[1],[2],[3],[4,5,13,14,15,16,17,7,8,9,10,11,12]]) (.forbid 0 6 0 (.forbid 0 1 4 (.cycle [0,6,7,8,9,10,11,12,2,1,16,15,14,13]) (certificate_532_part_8)) (.forbid 0 6 1 (certificate_532_part_10) (certificate_532_part_16))))))))

noncomputable def certificate_532_part_6 : FiniteCertificate := .forbid 3 5 1 (.system [[0],[1],[2],[3,13,5,6,7,8,9,10,11,12],[4]]) (.forbid 3 5 2 (.system [[0],[1],[2],[3,13,14,5,6,7,8,9,10,11,12],[4]]) (.forbid 3 5 3 (.system [[0],[1],[2],[3,13,14,15,5,6,7,8,9,10,11,12],[4]]) (.forbid 3 7 3 (.system [[0],[1],[2],[3,13,14,15,7,8,9,10,11,12],[4]]) (.forbid 3 7 4 (.system [[0],[1],[2],[3,13,14,15,16,7,8,9,10,11,12],[4]]) (.forbid 4 5 1 (.system [[0],[1],[2],[3],[4,13,5,6,7,8,9,10,11,12]]) (.forbid 4 5 2 (.system [[0],[1],[2],[3],[4,13,14,5,6,7,8,9,10,11,12]]) (.forbid 4 5 3 (.system [[0],[1],[2],[3],[4,13,14,15,5,6,7,8,9,10,11,12]]) (certificate_532_part_7))))))))

noncomputable def certificate_532_part_5 : FiniteCertificate := .forbid 1 7 6 (.system [[0],[1,13,14,15,16,17,18,7,6,5,4],[2],[3],[12]]) (.forbid 2 3 1 (.system [[0],[1],[2,13,3],[4,5,6,7,8,9,10,11,12]]) (.forbid 2 4 1 (.system [[0],[1],[2,13,4,5,6,7,8,9,10,11,12],[3]]) (.forbid 2 5 1 (.system [[0],[1],[2,13,5,6,7,8,9,10,11,12],[3],[4]]) (.forbid 2 5 2 (.system [[0],[1],[2,13,14,5,6,7,8,9,10,11,12],[3],[4]]) (.forbid 2 7 3 (.system [[0],[1],[2,13,14,15,7,8,9,10,11,12],[3],[4]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,13,4,5,6,7,8,9,10,11,12]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,13,14,4,5,6,7,8,9,10,11,12]]) (certificate_532_part_6))))))))

noncomputable def certificate_532_part_4 : FiniteCertificate := .forbid 1 5 1 (.system [[0],[1,13,5,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 5 2 (.system [[0],[1,13,14,5,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 5 3 (.system [[0],[1,13,14,15,5,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 5 4 (.system [[0],[1,13,14,15,16,5,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 5 5 (.system [[0],[1,13,14,15,16,17,5,6,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 7 3 (.system [[0],[1,13,14,15,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 7 4 (.system [[0],[1,13,14,15,16,7,8,9,10,11,12],[2],[3],[4]]) (.forbid 1 7 5 (.system [[0],[1,13,14,15,16,17,7,6,5,4],[2],[3],[12]]) (certificate_532_part_5))))))))

noncomputable def certificate_532_part_3 : FiniteCertificate := .forbid 1 2 3 (.system [[0],[1,13,14,15,2],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 3 1 (.system [[0],[1,13,3],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 3 2 (.system [[0],[1,13,14,3],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 3 3 (.system [[0],[1,13,14,15,3],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 4 1 (.system [[0],[1,13,4,5,6,7,8,9,10,11,12],[2],[3]]) (.forbid 1 4 2 (.system [[0],[1,13,14,4,5,6,7,8,9,10,11,12],[2],[3]]) (.forbid 1 4 3 (.system [[0],[1,13,14,15,4,5,6,7,8,9,10,11,12],[2],[3]]) (.forbid 1 4 4 (.system [[0],[1,13,14,15,16,4,5,6,7,8,9,10,11,12],[2],[3]]) (certificate_532_part_4))))))))

noncomputable def certificate_532_part_2 : FiniteCertificate := .forbid 0 4 3 (.system [[0,13,14,15,4,5,6,7,8,9,10,11,12],[1],[2],[3]]) (.forbid 0 4 4 (.system [[0,13,14,15,16,4,5,6,7,8,9,10,11,12],[1],[2],[3]]) (.forbid 0 7 3 (.system [[0,13,14,15,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 7 4 (.system [[0,13,14,15,16,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 7 5 (.system [[0,13,14,15,16,17,7,6,5,4],[1],[2],[3],[12]]) (.forbid 0 7 6 (.system [[0,13,14,15,16,17,18,7,6,5,4],[1],[2],[3],[12]]) (.forbid 1 2 1 (.system [[0],[1,13,2],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 2 2 (.system [[0],[1,13,14,2],[3],[4,5,6,7,8,9,10,11,12]]) (certificate_532_part_3))))))))

noncomputable def certificate_532_part_1 : FiniteCertificate := .forbid 0 3 3 (.system [[0,13,14,15,3],[1],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 5 1 (.system [[0,13,5,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 5 2 (.system [[0,13,14,5,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 5 3 (.system [[0,13,14,15,5,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 5 4 (.system [[0,13,14,15,16,5,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 5 5 (.system [[0,13,14,15,16,17,5,6,7,8,9,10,11,12],[1],[2],[3],[4]]) (.forbid 0 4 1 (.system [[0,13,4,5,6,7,8,9,10,11,12],[1],[2],[3]]) (.forbid 0 4 2 (.system [[0,13,14,4,5,6,7,8,9,10,11,12],[1],[2],[3]]) (certificate_532_part_2))))))))

noncomputable def certificate_532 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1],[2],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1],[2],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1],[2],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 2 1 (.system [[0,13,2],[1],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 2 2 (.system [[0,13,14,2],[1],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 2 3 (.system [[0,13,14,15,2],[1],[3],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 3 1 (.system [[0,13,3],[1],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3],[1],[2],[4,5,6,7,8,9,10,11,12]]) (certificate_532_part_1))))))))

noncomputable def certificate_538_part_1_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_538_M))))))))))))))))

noncomputable def certificate_538_part_2_M : ForbiddenMatrix := ((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,4,1) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_538_part_1_M))))))))))))))))

noncomputable def certificate_538_part_3_M : ForbiddenMatrix := ((1,2,2) :: (((1,2,1) :: (((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,5,5) :: (certificate_538_part_2_M))))))))))))))))

noncomputable def certificate_538_part_4_M : ForbiddenMatrix := ((1,5,2) :: (((1,4,1) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,4) :: (((1,2,3) :: (certificate_538_part_3_M))))))))))))))))

noncomputable def certificate_538_part_5_M : ForbiddenMatrix := ((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (certificate_538_part_4_M))))))))))))))))

noncomputable def certificate_538_part_6_M : ForbiddenMatrix := ((2,5,4) :: (((2,5,3) :: (((2,5,2) :: (((2,4,1) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (certificate_538_part_5_M))))))))))))))))

noncomputable def certificate_538_part_7_M : ForbiddenMatrix := ((3,5,2) :: (((3,4,1) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (((2,6,2) :: (((2,6,1) :: (((2,5,5) :: (certificate_538_part_6_M))))))))))))))))

noncomputable def certificate_538_part_8_M : ForbiddenMatrix := ((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (((3,6,1) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (certificate_538_part_7_M))))))))))))))))

noncomputable def certificate_538_part_9_M : ForbiddenMatrix := ((5,6,6) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (((4,6,1) :: (((4,5,1) :: (certificate_538_part_8_M))))))))))))))))

noncomputable def certificate_538_part_10_M : ForbiddenMatrix := ((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,6,6) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,0) :: (certificate_538_part_9_M))))))))))))))))

noncomputable def certificate_538_part_11_M : ForbiddenMatrix := ((1,7,6) :: (((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,7,2) :: (((1,6,6) :: (((0,7,6) :: (((0,7,5) :: (certificate_538_part_10_M))))))))))))))))

noncomputable def certificate_538_part_12_M : ForbiddenMatrix := ((6,7,2) :: (((6,7,1) :: (((4,7,1) :: (((3,7,4) :: (((3,7,3) :: (((3,7,2) :: (((2,7,3) :: (((2,7,2) :: (certificate_538_part_11_M))))))))))))))))

noncomputable def certificate_538_part_13_M : ForbiddenMatrix := ((0,7,1) :: (((0,1,6) :: (((0,1,5) :: (((6,7,6) :: (((6,7,5) :: (((6,7,4) :: (((6,7,3) :: (certificate_538_part_12_M))))))))))))))

noncomputable def certificate_538_part_14_M : ForbiddenMatrix := ((1,4,3) :: (((1,4,2) :: (((0,4,6) :: (((0,6,0) :: (((6,7,6) :: (((6,7,5) :: (((6,7,4) :: (((6,7,3) :: (certificate_538_part_12_M))))))))))))))))

noncomputable def certificate_538_part_15_M : ForbiddenMatrix := ((3,4,3) :: (((3,4,2) :: (((2,4,6) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((1,4,6) :: (((1,4,4) :: (certificate_538_part_14_M))))))))))))))))

noncomputable def certificate_538_part_16_M : ForbiddenMatrix := ((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))

noncomputable def certificate_538_part_17_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,5) :: (((0,3,6) :: (certificate_538_part_16_M))))))))))))))))

noncomputable def certificate_538_part_18_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((0,7,0) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))

noncomputable def certificate_538_part_19_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (certificate_538_part_18_M))))))))))))))))

noncomputable def certificate_538_part_20_M : ForbiddenMatrix := ((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((0,8,0) :: (((0,7,0) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))

noncomputable def certificate_538_part_21_M : ForbiddenMatrix := ((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (certificate_538_part_20_M))))))))))))))))

noncomputable def certificate_538_part_22_M : ForbiddenMatrix := ((3,4,5) :: (((2,8,1) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,8,1) :: (((1,4,5) :: (((1,3,6) :: (certificate_538_part_21_M))))))))))))))))

noncomputable def certificate_538_part_23_M : ForbiddenMatrix := ((1,5,1) :: (((0,5,1) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))

noncomputable def certificate_538_part_24_M : ForbiddenMatrix := ((0,1,5) :: (((1,4,0) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))

noncomputable def certificate_538_part_25_M : ForbiddenMatrix := ((1,6,0) :: (((1,4,0) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))

noncomputable def certificate_538_part_26_M : ForbiddenMatrix := ((0,8,1) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_538_part_25_M))))))))))))))))

noncomputable def certificate_538_part_27_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((1,8,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (certificate_538_part_26_M))))))))))))))))

noncomputable def certificate_538_part_28_M : ForbiddenMatrix := ((1,7,0) :: (((1,6,0) :: (((1,4,0) :: (((0,9,0) :: (((0,8,0) :: (((0,7,0) :: (((3,4,6) :: (((3,4,4) :: (certificate_538_part_15_M))))))))))))))))

noncomputable def certificate_538_part_29_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_538_part_28_M))))))))))))))

noncomputable def certificate_538_part_30_M : ForbiddenMatrix := ((2,3,5) :: (((1,7,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (certificate_538_part_29_M))))))))))))))))

noncomputable def certificate_538_part_31_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((1,8,0) :: (certificate_538_part_28_M))))))))))))))

noncomputable def certificate_538_part_32_M : ForbiddenMatrix := ((1,8,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,5) :: (certificate_538_part_31_M))))))))))))))))

noncomputable def certificate_538_part_33_M : ForbiddenMatrix := ((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,6,6) :: (((2,4,0) :: (((1,9,0) :: (((1,8,0) :: (certificate_538_part_28_M))))))))))))))

noncomputable def certificate_538_part_34_M : ForbiddenMatrix := ((2,6,0) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,6,6) :: (((2,4,0) :: (((1,9,0) :: (((1,8,0) :: (certificate_538_part_28_M))))))))))))))))

noncomputable def certificate_538_part_35_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_538_part_34_M))))))))))))))

noncomputable def certificate_538_part_36_M : ForbiddenMatrix := ((2,3,5) :: (((1,8,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (certificate_538_part_35_M))))))))))))))))

noncomputable def certificate_538_part_37_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((2,7,0) :: (certificate_538_part_34_M))))))))))))))

noncomputable def certificate_538_part_38_M : ForbiddenMatrix := ((1,7,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (((0,4,5) :: (certificate_538_part_37_M))))))))))))))))

noncomputable def certificate_538_part_39_M : ForbiddenMatrix := ((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((2,8,0) :: (((2,7,0) :: (certificate_538_part_34_M))))))))))))))

noncomputable def certificate_538_part_40_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,5) :: (((0,3,6) :: (certificate_538_part_39_M))))))))))))))))

noncomputable def certificate_538_part_41_M : ForbiddenMatrix := ((3,11,1) :: (((2,11,1) :: (((1,11,1) :: (((0,11,1) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (certificate_538_part_34_M))))))))))))))

noncomputable def certificate_538_part_42_M : ForbiddenMatrix := ((1,2,5) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_538_part_41_M))))))))))))))))

noncomputable def certificate_538_part_43_M : ForbiddenMatrix := ((3,7,0) :: (((3,11,1) :: (((2,11,1) :: (((1,11,1) :: (((0,11,1) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (certificate_538_part_34_M))))))))))))))))

noncomputable def certificate_538_part_44_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_538_part_43_M))))))))))))))

noncomputable def certificate_538_part_45_M : ForbiddenMatrix := ((2,3,5) :: (((1,7,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (certificate_538_part_44_M))))))))))))))))

noncomputable def certificate_538_part_46_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((3,8,0) :: (certificate_538_part_43_M))))))))))))))

noncomputable def certificate_538_part_47_M : ForbiddenMatrix := ((1,8,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,5) :: (certificate_538_part_46_M))))))))))))))))

noncomputable def certificate_538_part_48_M : ForbiddenMatrix := ((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((3,9,0) :: (((3,8,0) :: (certificate_538_part_43_M))))))))))))))

noncomputable def certificate_538_part_49_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,9,1) :: (((0,4,5) :: (((0,3,6) :: (certificate_538_part_48_M))))))))))))))))

noncomputable def certificate_538_part_50_M : ForbiddenMatrix := ((4,6,5) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((3,6,6) :: (((3,10,0) :: (((3,9,0) :: (((3,8,0) :: (certificate_538_part_43_M))))))))))))))))

noncomputable def certificate_538_part_51_M : ForbiddenMatrix := ((4,7,3) :: (((4,7,2) :: (((4,6,6) :: (((4,5,6) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,11,0) :: (certificate_538_part_50_M))))))))))))))))

noncomputable def certificate_538_part_52_M : ForbiddenMatrix := ((5,7,6) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((4,7,6) :: (((4,7,5) :: (((4,7,4) :: (certificate_538_part_51_M))))))))))))))))

noncomputable def certificate_538_part_53_M : ForbiddenMatrix := ((2,5,1) :: (((1,7,1) :: (((1,5,1) :: (((0,7,1) :: (((0,5,6) :: (((0,5,1) :: (((0,4,5) :: (certificate_538_part_52_M))))))))))))))

noncomputable def certificate_538_part_54_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((4,6,0) :: (certificate_538_part_52_M))))))))))))))

noncomputable def certificate_538_part_55_M : ForbiddenMatrix := ((1,8,1) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,5) :: (certificate_538_part_54_M))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates018
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_544_part_1_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,2) :: (((0,1,1) :: (((0,3,5) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_544_M))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates088
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2789_part_1 : FiniteCertificate := .forbid 3 7 1 (.system [[0],[1,2,3,16,7,6,5],[8,9,10,11,12,13,14,15]]) (.forbid 4 5 1 (.system [[0],[1,2,3,4,16,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 4 6 1 (.system [[0],[1,2,3,4,16,6,5],[8,9,10,11,12,13,14,15]]) (.forbid 4 6 2 (.system [[0],[1,2,3,4,16,17,6,5],[8,9,10,11,12,13],[15]]) (.forbid 4 6 3 (.system [[0],[1,2,3,4,16,17,18,6,5],[8,9,10,11],[13],[15]]) (.forbid 4 6 4 (.system [[0],[1],[3,4,16,17,18,19,6,5],[8,9,10,11],[13],[15]]) (.forbid 4 6 5 (.system [[0],[1,2,3,4,16,17,18,19,20,6,5],[8],[11],[13],[15]]) (.forbid 4 6 6 (.system [[0],[1],[3,4,16,17,18,19,20,21,6,5],[8],[11],[13],[15]]) (.forbid 4 7 1 (.system [[0],[1,2,3,4,16,7,6,5],[8,9,10,11,12,13],[15]]) (.forbid 4 7 2 (.system [[0],[1,2,3,4,16,17,7,6,5],[8,9,10,11],[13],[15]]) (.forbid 4 7 3 (.system [[0],[1],[3,4,16,17,18,7,6,5],[8,9,10,11],[13],[15]]) (.forbid 4 7 4 (.system [[0],[1,2,3,4,16,17,18,19,7,6,5],[8],[11],[13],[15]]) (.forbid 4 7 5 (.system [[0],[1],[3,4,16,17,18,19,20,7,6,5],[8],[11],[13],[15]]) (.forbid 4 7 6 (.system [[0],[1],[3,4,16,17,18,19,20,21,7,6,5],[8],[11],[13],[15]]) (.forbid 5 6 1 (.system [[0],[1,2,3,4,5,16,6,7,8,9,10,11,12,13],[15]]) (.forbid 6 7 1 (.system [[0],[1,2,3,4,5,6,16,7,8,9,10,11,12,13],[15]]) (.forbid 6 7 2 (.system [[0],[1,2,3,4,5,6,16,17,7,8,9,10,11],[13],[15]]) (.forbid 6 7 3 (.system [[0],[1,2,3],[5,6,16,17,18,7,8,9,10,11],[13],[15]]) (.forbid 6 7 4 (.system [[0],[1],[3],[5,6,16,17,18,19,7,8,9,10,11],[13],[15]]) (.forbid 6 7 5 (.system [[0],[1,2,3],[5,6,16,17,18,19,20,7,8],[11],[13],[15]]) (certificate_2789_part_0))))))))))))))))))))

noncomputable def certificate_2789_part_2 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1,2,16,17,4,3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 2 4 3 (.system [[0],[1,2,16,17,18,4,3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 2 4 4 (.system [[0],[1,2,16,17,18,19,4,3],[5,6,7,8],[11],[13],[15]]) (.forbid 2 4 5 (.system [[0],[1,2,16,17,18,19,20,4,3],[5,6,7,8],[11],[13],[15]]) (.forbid 2 4 6 (.system [[0],[1,2,16,17,18,19,20,21,4,3],[5],[8],[11],[13],[15]]) (.forbid 2 5 1 (.system [[0],[1,2,16,5,6,7,8,9,10,11,12,13,14,15],[3]]) (.forbid 2 6 1 (.system [[0],[1,2,16,6,5,4,3],[8,9,10,11,12,13,14,15]]) (.forbid 2 6 2 (.system [[0],[1,2,16,17,6,5,4,3],[8,9,10,11,12,13],[15]]) (.forbid 2 6 3 (.system [[0],[1,2,16,17,18,6,5,4,3],[8,9,10,11],[13],[15]]) (.forbid 2 6 4 (.system [[0],[1,2,16,17,18,19,6,5],[3],[8,9,10,11],[13],[15]]) (.forbid 2 6 5 (.system [[0],[1,2,16,17,18,19,20,6,5,4,3],[8],[11],[13],[15]]) (.forbid 2 6 6 (.system [[0],[1,2,16,17,18,19,20,21,6,5],[3],[8],[11],[13],[15]]) (.forbid 2 7 1 (.system [[0],[1,2,16,7,6,5,4,3],[8,9,10,11,12,13],[15]]) (.forbid 2 7 2 (.system [[0],[1,2,16,17,7,6,5,4,3],[8,9,10,11],[13],[15]]) (.forbid 2 7 3 (.system [[0],[1,2,16,17,18,7,6,5],[3],[8,9,10,11],[13],[15]]) (.forbid 2 7 4 (.system [[0],[1,2,16,17,18,19,7,6,5,4,3],[8],[11],[13],[15]]) (.forbid 2 7 5 (.system [[0],[1,2,16,17,18,19,20,7,6,5],[3],[8],[11],[13],[15]]) (.forbid 2 7 6 (.system [[0],[1,2,16,17,18,19,20,21,7,6,5],[3],[8],[11],[13],[15]]) (.forbid 3 4 1 (.system [[0],[1,2,3,16,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 3 6 1 (.system [[0],[1,2,3,16,6,7,8,9,10,11,12,13,14,15],[5]]) (certificate_2789_part_1))))))))))))))))))))

noncomputable def certificate_2789_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[1,16,17,18,4,3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 1 4 4 (.system [[0],[1,16,17,18,19,4,3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 1 4 5 (.system [[0],[1,16,17,18,19,20,4,3],[5,6,7,8],[11],[13],[15]]) (.forbid 1 4 6 (.system [[0],[1,16,17,18,19,20,21,4,3],[5,6,7,8],[11],[13],[15]]) (.forbid 1 6 1 (.system [[0],[5,4,3,2,1,16,6,7,8,9,10,11,12,13],[15]]) (.forbid 1 6 2 (.system [[0],[3,2,1,16,17,6,5],[8,9,10,11,12,13,14,15]]) (.forbid 1 6 3 (.system [[0],[3,2,1,16,17,18,6,5],[8,9,10,11,12,13],[15]]) (.forbid 1 6 4 (.system [[0],[3,2,1,16,17,18,19,6,5],[8,9,10,11],[13],[15]]) (.forbid 1 6 5 (.system [[0],[1,16,17,18,19,20,6,5],[3],[8,9,10,11],[13],[15]]) (.forbid 1 6 6 (.system [[0],[3,2,1,16,17,18,19,20,21,6,5],[8],[11],[13],[15]]) (.forbid 1 7 1 (.system [[0],[3,2,1,16,7,6,5],[8,9,10,11,12,13,14,15]]) (.forbid 1 7 2 (.system [[0],[3,2,1,16,17,7,6,5],[8,9,10,11,12,13],[15]]) (.forbid 1 7 3 (.system [[0],[3,2,1,16,17,18,7,6,5],[8,9,10,11],[13],[15]]) (.forbid 1 7 4 (.system [[0],[1,16,17,18,19,7,6,5],[3],[8,9,10,11],[13],[15]]) (.forbid 1 7 5 (.system [[0],[3,2,1,16,17,18,19,20,7,6,5],[8],[11],[13],[15]]) (.forbid 1 7 6 (.system [[0],[1,16,17,18,19,20,21,7,6,5],[3],[8],[11],[13],[15]]) (.forbid 1 9 1 (.system [[0],[8,7,6,5,4,3,2,1,16,9,10,11,12,13],[15]]) (.forbid 1 10 1 (.system [[0],[3,2,1,16,10,9,8,7,6,5],[11,12,13,14,15]]) (.forbid 2 3 1 (.system [[0],[1,2,16,3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 2 4 1 (.system [[0],[1,2,16,4,3],[5,6,7,8,9,10,11,12,13],[15]]) (certificate_2789_part_2))))))))))))))))))))

noncomputable def certificate_2789_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[0,16,17,18,6,5,4,3,2,1],[8,9,10,11],[13],[15]]) (.forbid 0 6 4 (.system [[0,16,17,18,19,6,5],[1,2,3],[8,9,10,11],[13],[15]]) (.forbid 0 6 5 (.system [[0,16,17,18,19,20,6,5],[1],[3],[8,9,10,11],[13],[15]]) (.forbid 0 6 6 (.system [[0,16,17,18,19,20,21,6,5],[1,2,3],[8],[11],[13],[15]]) (.forbid 0 7 1 (.system [[0,16,7,6,5,4,3,2,1],[8,9,10,11,12,13],[15]]) (.forbid 0 7 2 (.system [[0,16,17,7,6,5,4,3,2,1],[8,9,10,11],[13],[15]]) (.forbid 0 7 3 (.system [[0,16,17,18,7,6,5],[1,2,3],[8,9,10,11],[13],[15]]) (.forbid 0 7 4 (.system [[0,16,17,18,19,7,6,5],[1],[3],[8,9,10,11],[13],[15]]) (.forbid 0 7 5 (.system [[0,16,17,18,19,20,7,6,5],[1,2,3],[8],[11],[13],[15]]) (.forbid 0 7 6 (.system [[0,16,17,18,19,20,21,7,6,5],[1],[3],[8],[11],[13],[15]]) (.forbid 0 9 1 (.system [[0,16,9,10,11,12,13],[1,2,3,4,5,6,7,8],[15]]) (.forbid 0 10 1 (.system [[0,16,10,9,8,7,6,5,4,3,2,1],[11,12,13],[15]]) (.forbid 1 2 1 (.system [[0],[1,16,2,3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 1 2 2 (.system [[0],[1,16,17,2,3,4,5,6,7,8,9,10,11],[13],[15]]) (.forbid 1 2 3 (.system [[0],[1,16,17,18,2,3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 1 2 4 (.system [[0],[1,16,17,18,19,2,3,4,5,6,7,8],[11],[13],[15]]) (.forbid 1 2 5 (.system [[0],[1,16,17,18,19,20,2,3],[5,6,7,8],[11],[13],[15]]) (.forbid 1 2 6 (.system [[0],[1,16,17,18,19,20,21,2,3,4,5],[8],[11],[13],[15]]) (.forbid 1 4 1 (.system [[0],[1,16,4,3],[5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 1 4 2 (.system [[0],[1,16,17,4,3],[5,6,7,8,9,10,11,12,13],[15]]) (certificate_2789_part_3))))))))))))))))))))

noncomputable def certificate_2789 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2,3,4,5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2,3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1],[3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2,3],[5,6,7,8],[11],[13],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1],[3],[5,6,7,8],[11],[13],[15]]) (.forbid 0 2 1 (.system [[0,16,2,1],[3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 0 2 2 (.system [[0,16,17,2,1],[3,4,5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 2 3 (.system [[0,16,17,18,2,1],[3],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 2 4 (.system [[0,16,17,18,19,2,1],[3,4,5,6,7,8],[11],[13],[15]]) (.forbid 0 2 5 (.system [[0,16,17,18,19,20,2,1],[3],[5,6,7,8],[11],[13],[15]]) (.forbid 0 2 6 (.system [[0,16,17,18,19,20,21,2,1],[3,4,5],[8],[11],[13],[15]]) (.forbid 0 4 1 (.system [[0,16,4,3,2,1],[5,6,7,8,9,10,11,12,13],[15]]) (.forbid 0 4 2 (.system [[0,16,17,4,3,2,1],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 4 3 (.system [[0,16,17,18,4,3],[1],[5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 4 4 (.system [[0,16,17,18,19,4,3,2,1],[5,6,7,8],[11],[13],[15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[1],[5,6,7,8],[11],[13],[15]]) (.forbid 0 4 6 (.system [[0,16,17,18,19,20,21,4,3,2,1],[5],[8],[11],[13],[15]]) (.forbid 0 6 1 (.system [[0,16,6,7,8,9,10,11,12,13],[1,2,3,4,5],[15]]) (.forbid 0 6 2 (.system [[0,16,17,6,5,4,3,2,1],[8,9,10,11,12,13],[15]]) (certificate_2789_part_4))))))))))))))))))))

noncomputable def certificate_2813_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[1,16,17,18,4,3],[6],[7,8,9,10],[12,13,14,15]]) (.forbid 1 4 4 (.system [[0],[1,16,17,18,19,4,3],[6],[7,8,9,10,11,12],[15]]) (.forbid 1 4 5 (.system [[0],[1,16,17,18,19,20,4,3],[6],[7,8,9,10],[12],[15]]) (.forbid 1 4 6 (.system [[0],[1,16,17,18,19,20,21,4,3],[6],[7,8,9,10],[12],[15]]) (.forbid 1 5 1 (.system [[0],[1,16,5,4,3],[6],[7,8,9,10,11,12,13,14,15]]) (.forbid 1 5 2 (.system [[0],[1,16,17,5,4,3],[6],[7,8,9,10],[12,13,14,15]]) (.forbid 1 5 3 (.system [[0],[1,16,17,18,5,4,3],[6],[7,8,9,10,11,12],[15]]) (.forbid 1 5 4 (.system [[0],[1,16,17,18,19,5,4,3],[6],[7,8,9,10],[12],[15]]) (.forbid 1 5 5 (.system [[0],[1,16,17,18,19,20,5,4,3],[6],[7,8,9,10],[12],[15]]) (.forbid 1 5 6 (.system [[0],[1,16,17,18,19,20,21,5,4,3],[6],[7],[10],[12],[15]]) (.forbid 1 7 1 (.system [[0],[6,5,4,3,2,1,16,7,8,9,10,11,12,13,14,15]]) (.forbid 1 7 2 (.system [[0],[1,16,17,7,8,9,10],[3,4,5,6],[12,13,14,15]]) (.forbid 1 7 3 (.system [[0],[6,5,4,3,2,1,16,17,18,7,8,9,10],[12],[15]]) (.forbid 1 7 4 (.system [[0],[1,16,17,18,19,7,8,9,10],[3,4,5,6],[12],[15]]) (.forbid 1 7 5 (.system [[0],[6,5,4,3,2,1,16,17,18,19,20,7],[10],[12],[15]]) (.forbid 1 7 6 (.system [[0],[1,16,17,18,19,20,21,7],[3,4,5,6],[10],[12],[15]]) (.forbid 1 8 1 (.system [[0],[6,5,4,3,2,1,16,8,9,10],[7],[12,13,14,15]]) (.forbid 1 9 1 (.system [[0],[6,5,4,3,2,1,16,9,8,7],[10],[12,13,14,15]]) (.forbid 2 3 1 (.system [[0],[1,2,16,3,4,5,6],[7,8,9,10],[12,13,14,15]]) (.forbid 2 4 1 (.system [[0],[1,2,16,4,3],[6],[7,8,9,10,11,12,13,14,15]]) (certificate_2813_part_2))))))))))))))))))))

noncomputable def certificate_2813_part_4 : FiniteCertificate := .forbid 0 5 3 (.system [[0,16,17,18,5,4,3,2,1],[6],[7,8,9,10],[12],[15]]) (.forbid 0 5 4 (.system [[0,16,17,18,19,5,4,3],[1],[6],[7,8,9,10],[12],[15]]) (.forbid 0 5 5 (.system [[0,16,17,18,19,20,5,4,3,2,1],[6],[7],[10],[12],[15]]) (.forbid 0 5 6 (.system [[0,16,17,18,19,20,21,5,4,3],[1],[6],[7],[10],[12],[15]]) (.forbid 0 6 1 (.system [[0,16,6,5,4,3,2,1],[7,8,9,10,11,12,13,14,15]]) (.forbid 0 7 1 (.system [[0,16,7,8,9,10,11,12,13,14,15],[1,2,3,4,5,6]]) (.forbid 0 7 2 (.system [[0,16,17,7,8,9,10],[1],[3,4,5,6],[12,13,14,15]]) (.forbid 0 7 3 (.system [[0,16,17,18,7,8,9,10],[1,2,3,4,5,6],[12],[15]]) (.forbid 0 7 4 (.system [[0,16,17,18,19,7,8,9,10],[1],[3,4,5,6],[12],[15]]) (.forbid 0 7 5 (.system [[0,16,17,18,19,20,7],[1,2,3,4,5,6],[10],[12],[15]]) (.forbid 0 7 6 (.system [[0,16,17,18,19,20,21,7],[1],[3,4,5,6],[10],[12],[15]]) (.forbid 0 8 1 (.system [[0,16,8,9,10],[1,2,3,4,5,6],[7],[12,13,14,15]]) (.forbid 1 2 1 (.system [[0],[1,16,2,3,4,5,6],[7,8,9,10],[12,13,14,15]]) (.forbid 1 2 2 (.system [[0],[1,16,17,2,3,4,5,6],[7,8,9,10,11,12],[15]]) (.forbid 1 2 3 (.system [[0],[1,16,17,18,2,3,4,5,6],[7,8,9,10],[12],[15]]) (.forbid 1 2 4 (.system [[0],[1,16,17,18,19,2,3,4,5,6],[7,8,9,10],[12],[15]]) (.forbid 1 2 5 (.system [[0],[1,16,17,18,19,20,2,3,4,5,6],[7],[10],[12],[15]]) (.forbid 1 2 6 (.system [[0],[1,16,17,18,19,20,21,2,3,4,5,6],[7],[10],[12],[15]]) (.forbid 1 4 1 (.system [[0],[3,2,1,16,4,5,6],[7,8,9,10],[12,13,14,15]]) (.forbid 1 4 2 (.system [[0],[1,16,17,4,3],[6],[7,8,9,10,11,12,13,14,15]]) (certificate_2813_part_3))))))))))))))))))))

noncomputable def certificate_2813 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4,5,6],[7,8,9,10,11,12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1],[3,4,5,6],[7,8,9,10],[12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2,3,4,5,6],[7,8,9,10],[12],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1],[3,4,5,6],[7,8,9,10],[12],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2,3,4,5,6],[7],[10],[12],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1],[3,4,5,6],[7],[10],[12],[15]]) (.forbid 0 2 1 (.system [[0,16,2,1],[3,4,5,6],[7,8,9,10],[12,13,14,15]]) (.forbid 0 2 2 (.system [[0,16,17,2,1],[3,4,5,6],[7,8,9,10,11,12],[15]]) (.forbid 0 2 3 (.system [[0,16,17,18,2,1],[3,4,5,6],[7,8,9,10],[12],[15]]) (.forbid 0 2 4 (.system [[0,16,17,18,19,2,1],[3,4,5,6],[7,8,9,10],[12],[15]]) (.forbid 0 2 5 (.system [[0,16,17,18,19,20,2,1],[3,4,5,6],[7],[10],[12],[15]]) (.forbid 0 2 6 (.system [[0,16,17,18,19,20,21,2,1],[3,4,5,6],[7],[10],[12],[15]]) (.forbid 0 4 1 (.system [[0,16,4,5,6],[1,2,3],[7,8,9,10],[12,13,14,15]]) (.forbid 0 4 2 (.system [[0,16,17,4,3,2,1],[6],[7,8,9,10],[12,13,14,15]]) (.forbid 0 4 3 (.system [[0,16,17,18,4,3],[1],[6],[7,8,9,10],[12,13,14,15]]) (.forbid 0 4 4 (.system [[0,16,17,18,19,4,3,2,1],[6],[7,8,9,10],[12],[15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[1],[6],[7,8,9,10],[12],[15]]) (.forbid 0 4 6 (.system [[0,16,17,18,19,20,21,4,3,2,1],[6],[7],[10],[12],[15]]) (.forbid 0 5 1 (.system [[0,16,5,4,3,2,1],[6],[7,8,9,10],[12,13,14,15]]) (.forbid 0 5 2 (.system [[0,16,17,5,4,3],[1],[6],[7,8,9,10],[12,13,14,15]]) (certificate_2813_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates089
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2817_part_1 : FiniteCertificate := .forbid 4 5 1 (.system [[0],[1,2,3,4,16,5,6,7,8],[9],[11,12,13,14,15]]) (.forbid 4 5 2 (.system [[0],[1,2,3,4,16,17,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 4 5 3 (.system [[0],[1],[3,4,16,17,18,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 4 5 4 (.system [[0],[1],[3,4,16,17,18,19,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 4 5 5 (.system [[0],[1,2,3,4,16,17,18,19,20,5,6],[8],[9],[11],[15]]) (.forbid 4 5 6 (.system [[0],[1],[3,4,16,17,18,19,20,21,5,6],[8],[9],[11],[15]]) (.forbid 4 7 1 (.system [[0],[1,2,3,4,16,7,6],[8],[9,10,11,12,13,14,15]]) (.forbid 4 7 2 (.system [[0],[1,2,3,4,16,17,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 4 7 3 (.system [[0],[1],[3,4,16,17,18,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 4 7 4 (.system [[0],[1],[3,4,16,17,18,19,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 4 7 5 (.system [[0],[1,2,3,4,16,17,18,19,20,7,6],[8],[9],[11],[15]]) (.forbid 4 7 6 (.system [[0],[1],[3,4,16,17,18,19,20,21,7,6],[8],[9],[11],[15]]) (.forbid 4 8 1 (.system [[0],[1,2,3],[6,5,4,16,8],[9,10,11,12,13,14,15]]) (.forbid 5 6 1 (.system [[0],[1,2,3,4,5,16,6,7,8],[9],[11,12,13,14,15]]) (.forbid 5 7 1 (.system [[0],[1,2,3,4,5,16,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 5 7 2 (.system [[0],[1],[3,4,5,16,17,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 5 7 3 (.system [[0],[1],[3,4,5,16,17,18,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 5 7 4 (.system [[0],[1,2,3,4,5,16,17,18,19,7,6],[8],[9],[11],[15]]) (.forbid 5 7 5 (.system [[0],[1],[3,4,5,16,17,18,19,20,7,6],[8],[9],[11],[15]]) (.forbid 5 7 6 (.system [[0],[1],[3,4,5,16,17,18,19,20,21,7,6],[8],[9],[11],[15]]) (certificate_2817_part_0))))))))))))))))))))

noncomputable def certificate_2817_part_2 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1,2,16,17,4,3],[6,7,8],[9],[11,12,13,14,15]]) (.forbid 2 4 3 (.system [[0],[1,2,16,17,18,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 2 4 4 (.system [[0],[1,2,16,17,18,19,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 2 4 5 (.system [[0],[1,2,16,17,18,19,20,4,3],[6,7,8],[9],[11],[15]]) (.forbid 2 4 6 (.system [[0],[1,2,16,17,18,19,20,21,4,3],[6],[8],[9],[11],[15]]) (.forbid 2 5 1 (.system [[0],[1,2,16,5,4,3],[6,7,8],[9],[11,12,13,14,15]]) (.forbid 2 5 2 (.system [[0],[1,2,16,17,5,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 2 5 3 (.system [[0],[1,2,16,17,18,5,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 2 5 4 (.system [[0],[1,2,16,17,18,19,5,4,3],[6,7,8],[9],[11],[15]]) (.forbid 2 5 5 (.system [[0],[1,2,16,17,18,19,20,5,4,3],[6],[8],[9],[11],[15]]) (.forbid 2 5 6 (.system [[0],[1,2,16,17,18,19,20,21,5,4,3],[6],[8],[9],[11],[15]]) (.forbid 2 6 1 (.system [[0],[1,2,16,6,5,4,3],[8],[9,10,11,12,13,14,15]]) (.forbid 2 7 1 (.system [[0],[1,2,16,7,6,5,4,3],[8],[9],[11,12,13,14,15]]) (.forbid 2 7 2 (.system [[0],[1,2,16,17,7,6,5,4,3],[8],[9],[11,12,13,14,15]]) (.forbid 2 7 3 (.system [[0],[1,2,16,17,18,7,6],[3],[8],[9],[11,12,13,14,15]]) (.forbid 2 7 4 (.system [[0],[1,2,16,17,18,19,7,6,5,4,3],[8],[9],[11],[15]]) (.forbid 2 7 5 (.system [[0],[1,2,16,17,18,19,20,7,6,5,4,3],[8],[9],[11],[15]]) (.forbid 2 7 6 (.system [[0],[1,2,16,17,18,19,20,21,7,6],[3],[8],[9],[11],[15]]) (.forbid 3 4 1 (.system [[0],[1,2,3,16,4,5,6,7,8],[9],[11,12,13,14,15]]) (.forbid 3 7 1 (.system [[0],[1],[6,5,4,3,16,7,8],[9,10,11,12,13,14,15]]) (certificate_2817_part_1))))))))))))))))))))

noncomputable def certificate_2817_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[1,16,17,18,4,3],[6,7,8],[9],[11,12,13,14,15]]) (.forbid 1 4 4 (.system [[0],[1,16,17,18,19,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 1 4 5 (.system [[0],[1,16,17,18,19,20,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 1 4 6 (.system [[0],[1,16,17,18,19,20,21,4,3],[6,7,8],[9],[11],[15]]) (.forbid 1 5 1 (.system [[0],[1,16,5,4,3],[6,7,8],[9,10,11,12,13,14,15]]) (.forbid 1 5 2 (.system [[0],[1,16,17,5,4,3],[6,7,8],[9],[11,12,13,14,15]]) (.forbid 1 5 3 (.system [[0],[1,16,17,18,5,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 1 5 4 (.system [[0],[1,16,17,18,19,5,4,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 1 5 5 (.system [[0],[1,16,17,18,19,20,5,4,3],[6,7,8],[9],[11],[15]]) (.forbid 1 5 6 (.system [[0],[1,16,17,18,19,20,21,5,4,3],[6],[8],[9],[11],[15]]) (.forbid 1 7 1 (.system [[0],[1,16,7,6,5,4,3],[8],[9,10,11,12,13,14,15]]) (.forbid 1 7 2 (.system [[0],[1,16,17,7,6,5,4,3],[8],[9],[11,12,13,14,15]]) (.forbid 1 7 3 (.system [[0],[3,2,1,16,17,18,7,6],[8],[9],[11,12,13,14,15]]) (.forbid 1 7 4 (.system [[0],[1,16,17,18,19,7,6],[3],[8],[9],[11,12,13,14,15]]) (.forbid 1 7 5 (.system [[0],[1,16,17,18,19,20,7,6,5,4,3],[8],[9],[11],[15]]) (.forbid 1 7 6 (.system [[0],[3,2,1,16,17,18,19,20,21,7,6],[8],[9],[11],[15]]) (.forbid 1 9 1 (.system [[0],[8,7,6,5,4,3,2,1,16,9,10,11,12,13,14,15]]) (.forbid 1 10 1 (.system [[0],[6,5,4,3,2,1,16,10,9],[8],[11,12,13,14,15]]) (.forbid 2 3 1 (.system [[0],[1,2,16,3,4,5,6,7,8],[9],[11,12,13,14,15]]) (.forbid 2 4 1 (.system [[0],[1,2,16,4,3],[6,7,8],[9,10,11,12,13,14,15]]) (certificate_2817_part_2))))))))))))))))))))

noncomputable def certificate_2817_part_4 : FiniteCertificate := .forbid 0 5 3 (.system [[0,16,17,18,5,4,3],[1],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 5 4 (.system [[0,16,17,18,19,5,4,3],[1],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 5 5 (.system [[0,16,17,18,19,20,5,4,3,2,1],[6],[8],[9],[11],[15]]) (.forbid 0 5 6 (.system [[0,16,17,18,19,20,21,5,4,3],[1],[6],[8],[9],[11],[15]]) (.forbid 0 7 1 (.system [[0,16,7,6,5,4,3,2,1],[8],[9],[11,12,13,14,15]]) (.forbid 0 7 2 (.system [[0,16,17,7,6,5,4,3],[1],[8],[9],[11,12,13,14,15]]) (.forbid 0 7 3 (.system [[0,16,17,18,7,6],[1,2,3],[8],[9],[11,12,13,14,15]]) (.forbid 0 7 4 (.system [[0,16,17,18,19,7,6],[1],[3],[8],[9],[11,12,13,14,15]]) (.forbid 0 7 5 (.system [[0,16,17,18,19,20,7,6,5,4,3],[1],[8],[9],[11],[15]]) (.forbid 0 7 6 (.system [[0,16,17,18,19,20,21,7,6],[1,2,3],[8],[9],[11],[15]]) (.forbid 0 8 1 (.system [[0,16,8,7,6,5,4,3,2,1],[9,10,11,12,13,14,15]]) (.forbid 0 9 1 (.system [[0,16,9,10,11,12,13,14,15],[1,2,3,4,5,6,7,8]]) (.forbid 1 2 1 (.system [[0],[1,16,2,3,4,5,6,7,8],[9],[11,12,13,14,15]]) (.forbid 1 2 2 (.system [[0],[1,16,17,2,3,4,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 1 2 3 (.system [[0],[1,16,17,18,2,3,4,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 1 2 4 (.system [[0],[1,16,17,18,19,2,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 1 2 5 (.system [[0],[1,16,17,18,19,20,2,3,4,5,6],[8],[9],[11],[15]]) (.forbid 1 2 6 (.system [[0],[1,16,17,18,19,20,21,2,3,4,5,6],[8],[9],[11],[15]]) (.forbid 1 4 1 (.system [[0],[3,2,1,16,4,5,6,7,8],[9],[11,12,13,14,15]]) (.forbid 1 4 2 (.system [[0],[1,16,17,4,3],[6,7,8],[9,10,11,12,13,14,15]]) (certificate_2817_part_3))))))))))))))))))))

noncomputable def certificate_2817 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4,5,6,7,8],[9,10,11,12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2,3,4,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1],[3,4,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2,3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1],[3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1],[3,4,5,6],[8],[9],[11],[15]]) (.forbid 0 2 1 (.system [[0,16,2,1],[3,4,5,6,7,8],[9],[11,12,13,14,15]]) (.forbid 0 2 2 (.system [[0,16,17,2,1],[3,4,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 0 2 3 (.system [[0,16,17,18,2,1],[3,4,5,6],[8],[9],[11,12,13,14,15]]) (.forbid 0 2 4 (.system [[0,16,17,18,19,2,1],[3],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 2 5 (.system [[0,16,17,18,19,20,2,1],[3,4,5,6],[8],[9],[11],[15]]) (.forbid 0 2 6 (.system [[0,16,17,18,19,20,21,2,1],[3,4,5,6],[8],[9],[11],[15]]) (.forbid 0 4 1 (.system [[0,16,4,5,6,7,8],[1,2,3],[9],[11,12,13,14,15]]) (.forbid 0 4 2 (.system [[0,16,17,4,3,2,1],[6,7,8],[9],[11,12,13,14,15]]) (.forbid 0 4 3 (.system [[0,16,17,18,4,3,2,1],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 4 4 (.system [[0,16,17,18,19,4,3],[1],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[1],[6],[8],[9],[11,12,13,14,15]]) (.forbid 0 4 6 (.system [[0,16,17,18,19,20,21,4,3,2,1],[6],[8],[9],[11],[15]]) (.forbid 0 5 1 (.system [[0,16,5,4,3,2,1],[6,7,8],[9],[11,12,13,14,15]]) (.forbid 0 5 2 (.system [[0,16,17,5,4,3,2,1],[6],[8],[9],[11,12,13,14,15]]) (certificate_2817_part_4))))))))))))))))))))

noncomputable def certificate_2838 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2,3,4,5,6,7],[8,9,10,11,12,13,14,15,16]]) (.forbid 0 1 2 (.system [[0,17,18,1,2,3,4,5,6,7],[8],[10,11,12,13,14],[16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1],[3,4,5,6,7],[8],[10,11,12,13,14],[16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1],[3,4,5,6,7],[8],[10,11,12,13,14],[16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2,3,4,5,6,7],[8],[10],[14],[16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1],[3,4,5,6,7],[8],[10],[14],[16]]) (.forbid 0 2 1 (.system [[0,17,2,1],[3,4,5,6,7],[8,9,10,11,12,13,14],[16]]) (.forbid 0 2 2 (.system [[0,17,18,2,1],[3,4,5,6,7],[8],[10,11,12,13,14],[16]]) (.forbid 0 2 3 (.system [[0,17,18,19,2,1],[3,4,5,6,7],[8],[10,11,12,13,14],[16]]) (.forbid 0 2 4 (.system [[0,17,18,19,20,2,1],[3,4,5,6,7],[8,9,10],[14],[16]]) (.forbid 0 2 5 (.system [[0,17,18,19,20,21,2,1],[3,4,5,6,7],[8],[10],[14],[16]]) (.forbid 0 2 6 (.system [[0,17,18,19,20,21,22,2,1],[3,4,5,6,7],[8],[10],[14],[16]]) (.forbid 0 4 1 (.system [[0,17,4,5,6,7],[1,2,3],[8,9,10,11,12,13,14],[16]]) (.forbid 0 4 2 (.system [[0,17,18,4,5,6,7],[1,2,3],[8],[10,11,12,13,14],[16]]) (.forbid 0 4 3 (.system [[0,17,18,19,4,3,2,1],[7],[8,9,10,11,12,13,14],[16]]) (.forbid 0 4 4 (.system [[0,17,18,19,20,4,3,2,1],[7],[8],[10,11,12,13,14],[16]]) (.forbid 0 4 5 (.system [[0,17,18,19,20,21,4,3],[1],[7],[8],[10,11,12,13,14],[16]]) (.forbid 0 4 6 (.system [[0,17,18,19,20,21,22,4,3],[1],[7],[8],[10,11,12,13,14],[16]]) (.forbid 0 6 1 (.system [[0,17,6,5,4,3,2,1],[7],[8,9,10,11,12,13,14],[16]]) (.forbid 0 7 1 (.system [[0,17,7,6,5,4,3,2,1],[8,9,10,11,12,13,14,15,16]]) (certificate_2838_part_4))))))))))))))))))))

noncomputable def certificate_2839_part_1 : FiniteCertificate := .forbid 4 5 1 (.system [[0],[1],[3,4,16,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 4 8 1 (.system [[0],[1],[3],[7,6,5,4,16,8,9,10,11],[12,13,14,15]]) (.forbid 4 8 2 (.system [[0],[1,2,3],[7,6,5,4,16,17,8,9,10,11],[12],[15]]) (.forbid 4 8 3 (.system [[0],[1],[3,4,16,17,18,8,9,10,11],[7],[12,13,14,15]]) (.forbid 4 8 4 (.system [[0],[1,2,3,4,16,17,18,19,8,9,10,11],[7],[12],[15]]) (.forbid 4 8 5 (.system [[0],[1],[3,4,16,17,18,19,20,8,9,10,11],[7],[12],[15]]) (.forbid 4 8 6 (.system [[0],[1,2,3,4,16,17,18,19,20,21,8],[7],[11],[12],[15]]) (.forbid 4 9 1 (.system [[0],[1,2,3],[7,6,5,4,16,9,8],[11],[12,13,14,15]]) (.forbid 4 9 2 (.system [[0],[1,2,3,4,16,17,9,10,11],[7],[8],[12,13,14,15]]) (.forbid 4 9 3 (.system [[0],[1,2,3,4,16,17,18,9,8],[7],[11],[12,13,14,15]]) (.forbid 4 9 4 (.system [[0],[1],[3,4,16,17,18,19,9,8],[7],[11],[12,13,14,15]]) (.forbid 4 9 5 (.system [[0],[1,2,3,4,16,17,18,19,20,9,8],[7],[11],[12],[15]]) (.forbid 4 9 6 (.system [[0],[1],[3,4,16,17,18,19,20,21,9,8],[7],[11],[12],[15]]) (.forbid 5 9 1 (.system [[0],[1,2,3,4,5,16,9,10,11],[7],[8],[12,13,14,15]]) (.forbid 6 8 1 (.system [[0],[1],[3,4,5,6,16,8,9,10,11],[7],[12,13,14,15]]) (.forbid 7 8 1 (.system [[0],[1,2,3,4,5,6,7,16,8,9,10,11],[12,13,14,15]]) (.forbid 8 9 1 (.system [[0],[1],[3,4,5,6,7],[8,16,9,10,11],[12,13,14,15]]) (.forbid 8 9 2 (.system [[0],[1,2,3,4,5,6,7],[8,16,17,9,10,11],[12],[15]]) (.forbid 8 9 3 (.system [[0],[1],[3,4,5,6,7],[8,16,17,18,9,10,11],[12],[15]]) (.forbid 8 9 4 (.system [[0],[1],[3,4,5,6,7],[8,16,17,18,19,9,10,11],[12],[15]]) (certificate_2839_part_0))))))))))))))))))))

noncomputable def certificate_2839_part_2 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1,2,16,17,4,3],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 2 4 3 (.system [[0],[1,2,16,17,18,4,3],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 2 4 4 (.system [[0],[1,2,16,17,18,19,4,3],[7],[8,9,10,11],[12],[15]]) (.forbid 2 4 5 (.system [[0],[1,2,16,17,18,19,20,4,3],[7],[8,9,10,11],[12],[15]]) (.forbid 2 4 6 (.system [[0],[1,2,16,17,18,19,20,21,4,3],[7],[8],[11],[12],[15]]) (.forbid 2 5 1 (.system [[0],[1,2,16,5,4,3],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 2 8 1 (.system [[0],[1,2,16,8,9,10,11],[3,4,5,6,7],[12,13,14,15]]) (.forbid 2 8 2 (.system [[0],[1,2,16,17,8,9,10,11],[3,4,5,6,7],[12],[15]]) (.forbid 2 8 3 (.system [[0],[1,2,16,17,18,8,9,10,11],[3,4,5,6,7],[12],[15]]) (.forbid 2 8 4 (.system [[0],[1,2,16,17,18,19,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 2 8 5 (.system [[0],[1,2,16,17,18,19,20,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 2 8 6 (.system [[0],[1,2,16,17,18,19,20,21,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 2 9 1 (.system [[0],[1,2,16,9,8],[3,4,5,6,7],[11],[12,13,14,15]]) (.forbid 2 9 2 (.system [[0],[1,2,16,17,9,8],[3,4,5,6,7],[11],[12,13,14,15]]) (.forbid 2 9 3 (.system [[0],[1,2,16,17,18,9,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 2 9 4 (.system [[0],[1,2,16,17,18,19,9,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 2 9 5 (.system [[0],[1,2,16,17,18,19,20,9,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 2 9 6 (.system [[0],[1,2,16,17,18,19,20,21,9,8],[3],[7],[11],[12],[15]]) (.forbid 3 4 1 (.system [[0],[1],[3,16,4,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 3 9 1 (.system [[0],[1],[7,6,5,4,3,16,9,10,11],[8],[12,13,14,15]]) (certificate_2839_part_1))))))))))))))))))))

noncomputable def certificate_2839_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[1,16,17,18,4,3],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 1 4 4 (.system [[0],[1,16,17,18,19,4,3],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 1 4 5 (.system [[0],[1,16,17,18,19,20,4,3],[7],[8,9,10,11],[12],[15]]) (.forbid 1 4 6 (.system [[0],[1,16,17,18,19,20,21,4,3],[7],[8,9,10,11],[12],[15]]) (.forbid 1 6 1 (.system [[0],[1,16,6,5,4,3],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 1 8 1 (.system [[0],[7,6,5,4,3,2,1,16,8,9,10,11],[12,13,14,15]]) (.forbid 1 8 2 (.system [[0],[1,16,17,8,9,10,11],[3,4,5,6,7],[12,13,14,15]]) (.forbid 1 8 3 (.system [[0],[1,16,17,18,8,9,10,11],[3,4,5,6,7],[12],[15]]) (.forbid 1 8 4 (.system [[0],[7,6,5,4,3,2,1,16,17,18,19,8],[11],[12],[15]]) (.forbid 1 8 5 (.system [[0],[1,16,17,18,19,20,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 1 8 6 (.system [[0],[1,16,17,18,19,20,21,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 1 9 1 (.system [[0],[1,16,9,10,11],[3,4,5,6,7],[8],[12,13,14,15]]) (.forbid 1 9 2 (.system [[0],[1,16,17,9,8],[3,4,5,6,7],[11],[12,13,14,15]]) (.forbid 1 9 3 (.system [[0],[7,6,5,4,3,2,1,16,17,18,9,8],[11],[12],[15]]) (.forbid 1 9 4 (.system [[0],[1,16,17,18,19,9,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 1 9 5 (.system [[0],[1,16,17,18,19,20,9,8],[3,4,5,6,7],[11],[12],[15]]) (.forbid 1 9 6 (.system [[0],[3,2,1,16,17,18,19,20,21,9,8],[7],[11],[12],[15]]) (.forbid 1 10 1 (.system [[0],[1,16,10,9,8],[3,4,5,6,7],[11],[12,13,14,15]]) (.forbid 2 3 1 (.system [[0],[1,2,16,3,4,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 2 4 1 (.system [[0],[1,2,16,4,5,6,7],[3],[8,9,10,11],[12,13,14,15]]) (certificate_2839_part_2))))))))))))))))))))

noncomputable def certificate_2839_part_4 : FiniteCertificate := .forbid 0 8 1 (.system [[0,16,8,9,10,11],[1,2,3,4,5,6,7],[12,13,14,15]]) (.forbid 0 8 2 (.system [[0,16,17,8,9,10,11],[1],[3,4,5,6,7],[12,13,14,15]]) (.forbid 0 8 3 (.system [[0,16,17,18,8,9,10,11],[1],[3,4,5,6,7],[12],[15]]) (.forbid 0 8 4 (.system [[0,16,17,18,19,8],[1,2,3,4,5,6,7],[11],[12],[15]]) (.forbid 0 8 5 (.system [[0,16,17,18,19,20,8],[1],[3,4,5,6,7],[11],[12],[15]]) (.forbid 0 8 6 (.system [[0,16,17,18,19,20,21,8],[1],[3,4,5,6,7],[11],[12],[15]]) (.forbid 0 9 1 (.system [[0,16,9,10,11],[1],[3,4,5,6,7],[8],[12,13,14,15]]) (.forbid 0 9 2 (.system [[0,16,17,9,8],[1],[3,4,5,6,7],[11],[12,13,14,15]]) (.forbid 0 9 3 (.system [[0,16,17,18,9,8],[1,2,3,4,5,6,7],[11],[12],[15]]) (.forbid 0 9 4 (.system [[0,16,17,18,19,9,8],[1],[3,4,5,6,7],[11],[12],[15]]) (.forbid 0 9 5 (.system [[0,16,17,18,19,20,9,8],[1],[3,4,5,6,7],[11],[12],[15]]) (.forbid 0 9 6 (.system [[0,16,17,18,19,20,21,9,8],[1,2,3],[7],[11],[12],[15]]) (.forbid 1 2 1 (.system [[0],[1,16,2,3,4,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 1 2 2 (.system [[0],[1,16,17,2,3,4,5,6,7],[8,9,10,11],[12],[15]]) (.forbid 1 2 3 (.system [[0],[1,16,17,18,2,3,4,5,6,7],[8,9,10,11],[12],[15]]) (.forbid 1 2 4 (.system [[0],[1,16,17,18,19,2,3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 1 2 5 (.system [[0],[1,16,17,18,19,20,2,3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 1 2 6 (.system [[0],[1,16,17,18,19,20,21,2,3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 1 4 1 (.system [[0],[1,16,4,5,6,7],[3],[8,9,10,11],[12,13,14,15]]) (.forbid 1 4 2 (.system [[0],[3,2,1,16,17,4,5,6,7],[8,9,10,11],[12],[15]]) (certificate_2839_part_3))))))))))))))))))))

noncomputable def certificate_2839 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1],[3,4,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1],[3,4,5,6,7],[8,9,10,11],[12],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2,3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1],[3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1],[3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 0 2 1 (.system [[0,16,2,1],[3,4,5,6,7],[8,9,10,11],[12,13,14,15]]) (.forbid 0 2 2 (.system [[0,16,17,2,1],[3,4,5,6,7],[8,9,10,11],[12],[15]]) (.forbid 0 2 3 (.system [[0,16,17,18,2,1],[3,4,5,6,7],[8,9,10,11],[12],[15]]) (.forbid 0 2 4 (.system [[0,16,17,18,19,2,1],[3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 0 2 5 (.system [[0,16,17,18,19,20,2,1],[3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 0 2 6 (.system [[0,16,17,18,19,20,21,2,1],[3,4,5,6,7],[8],[11],[12],[15]]) (.forbid 0 4 1 (.system [[0,16,4,5,6,7],[1],[3],[8,9,10,11],[12,13,14,15]]) (.forbid 0 4 2 (.system [[0,16,17,4,5,6,7],[1,2,3],[8,9,10,11],[12],[15]]) (.forbid 0 4 3 (.system [[0,16,17,18,4,3],[1],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 0 4 4 (.system [[0,16,17,18,19,4,3,2,1],[7],[8,9,10,11],[12],[15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[1],[7],[8,9,10,11],[12],[15]]) (.forbid 0 4 6 (.system [[0,16,17,18,19,20,21,4,3,2,1],[7],[8],[11],[12],[15]]) (.forbid 0 6 1 (.system [[0,16,6,5,4,3],[1],[7],[8,9,10,11],[12,13,14,15]]) (.forbid 0 7 1 (.system [[0,16,7,6,5,4,3,2,1],[8,9,10,11],[12,13,14,15]]) (certificate_2839_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates090
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2861 : FiniteCertificate := .forbid 0 1 1 (.system [[0,15,1,2],[3,4,5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 1 2 (.system [[0,15,16,1,2],[3],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 1 3 (.system [[0,15,16,17,1,2],[3],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 1 4 (.system [[0,15,16,17,18,1,2],[3],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 1 5 (.system [[0,15,16,17,18,19,1,2],[3,4,5],[6],[8],[9],[14]]) (.forbid 0 1 6 (.system [[0,15,16,17,18,19,20,1,2],[3],[5],[6],[8],[9],[14]]) (.forbid 0 3 1 (.system [[2,1,0,15,3,4,5],[6,7,8],[9,10,11,12,13,14]]) (.forbid 0 3 2 (.system [[2,1,0,15,16,3],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 3 3 (.system [[0,15,16,17,3],[2],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 3 4 (.system [[0,15,16,17,18,3],[2],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 3 5 (.system [[0,15,16,17,18,19,3],[2],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 3 6 (.system [[2,1,0,15,16,17,18,19,20,3],[5],[6],[8],[9],[14]]) (.forbid 0 4 1 (.system [[2,1,0,15,4,3],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 4 2 (.system [[0,15,16,4,3],[2],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 4 3 (.system [[0,15,16,17,4,3],[2],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 4 4 (.system [[0,15,16,17,18,4,3],[2],[5],[6],[8],[9,10,11,12,13,14]]) (.forbid 0 4 5 (.system [[2,1,0,15,16,17,18,19,4,3],[5],[6],[8],[9],[14]]) (.forbid 0 4 6 (.system [[0,15,16,17,18,19,20,4,3],[2],[5],[6],[8],[9],[14]]) (.forbid 0 5 1 (.system [[2,1,0,15,5,4,3],[6,7,8],[9,10,11,12,13,14]]) (.forbid 0 6 1 (.system [[2,1,0,15,6,7,8],[3,4,5],[9,10,11,12,13,14]]) (certificate_2861_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates091
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2886_part_1 : FiniteCertificate := .forbid 3 8 1 (.system [[0,1,2],[3,16,8,7,6],[5],[9,10,11,12,13,14,15]]) (.forbid 4 5 1 (.system [[0],[2],[3,4,16,5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 4 6 1 (.system [[0],[2],[3,4,16,6,7,8,9,10,11,12,13,14,15],[5]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,16,17,6,7,8,9,10,11,12],[5],[15]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,16,17,18,6,7,8,9,10,11,12],[5],[15]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,16,17,18,19,6,7,8,9],[5],[12],[15]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,16,17,18,19,20,6,7,8,9],[5],[12],[15]]) (.forbid 4 6 6 (.system [[0,1,2],[3,4,16,17,18,19,20,21,6],[5],[9],[12],[15]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,16,7,6],[5],[9,10,11,12,13,14,15]]) (.forbid 4 7 2 (.system [[0],[2],[3,4,16,17,7,6],[5],[9,10,11,12,13,14,15]]) (.forbid 4 7 3 (.system [[0,1,2],[3,4,16,17,18,7,6],[5],[9,10,11,12],[15]]) (.forbid 4 7 4 (.system [[0],[2],[3,4,16,17,18,19,7,6],[5],[9,10,11,12],[15]]) (.forbid 4 7 5 (.system [[0,1,2],[3,4,16,17,18,19,20,7,6],[5],[9],[12],[15]]) (.forbid 4 7 6 (.system [[0],[2],[3,4,16,17,18,19,20,21,7,6],[5],[9],[12],[15]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,16,6,7,8,9,10,11,12,13,14,15]]) (.forbid 5 7 1 (.system [[0,1,2],[3],[5,16,7,8,9,10,11,12,13,14,15],[6]]) (.forbid 6 7 1 (.system [[0,1,2],[3],[5],[6,16,7,8,9,10,11,12,13,14,15]]) (.forbid 6 7 2 (.system [[0],[2],[3],[5],[6,16,17,7,8,9,10,11,12,13,14,15]]) (.forbid 6 7 3 (.system [[0,1,2],[3],[5],[6,16,17,18,7,8,9,10,11,12],[15]]) (.forbid 6 7 4 (.system [[0],[2],[3],[5],[6,16,17,18,19,7,8,9,10,11,12],[15]]) (certificate_2886_part_0))))))))))))))))))))

noncomputable def certificate_2886_part_2 : FiniteCertificate := .forbid 2 6 1 (.system [[0,1,2,16,6,7,8,9,10,11,12,13,14,15],[3,4,5]]) (.forbid 2 7 1 (.system [[0,1,2,16,7,8,9,10,11,12,13,14,15],[3],[5],[6]]) (.forbid 3 4 1 (.system [[0],[2],[3,16,4,5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 3 4 2 (.system [[0,1,2],[3,16,17,4,5],[6,7,8,9,10,11,12],[15]]) (.forbid 3 4 3 (.system [[0],[2],[3,16,17,18,4,5],[6,7,8,9,10,11,12],[15]]) (.forbid 3 4 4 (.system [[0,1,2],[3,16,17,18,19,4,5],[6,7,8,9],[12],[15]]) (.forbid 3 4 5 (.system [[0],[2],[3,16,17,18,19,20,4,5],[6,7,8,9],[12],[15]]) (.forbid 3 4 6 (.system [[0,1,2],[3,16,17,18,19,20,21,4,5],[6],[9],[12],[15]]) (.forbid 3 6 1 (.system [[0,1,2],[5,4,3,16,6,7,8,9,10,11,12,13,14,15]]) (.forbid 3 6 2 (.system [[0],[2],[3,16,17,6,7,8,9,10,11,12,13,14,15],[5]]) (.forbid 3 6 3 (.system [[0,1,2],[3,16,17,18,6,7,8,9,10,11,12],[5],[15]]) (.forbid 3 6 4 (.system [[0],[2],[3,16,17,18,19,6,7,8,9,10,11,12],[5],[15]]) (.forbid 3 6 5 (.system [[0,1,2],[3,16,17,18,19,20,6,7,8,9],[5],[12],[15]]) (.forbid 3 6 6 (.system [[0],[2],[3,16,17,18,19,20,21,6,7,8,9],[5],[12],[15]]) (.forbid 3 7 1 (.system [[0,1,2],[3,16,7,8,9,10,11,12,13,14,15],[5],[6]]) (.forbid 3 7 2 (.system [[0,1,2],[3,16,17,7,6],[5],[9,10,11,12,13,14,15]]) (.forbid 3 7 3 (.system [[0],[2],[3,16,17,18,7,6],[5],[9,10,11,12,13,14,15]]) (.forbid 3 7 4 (.system [[0,1,2],[3,16,17,18,19,7,6],[5],[9,10,11,12],[15]]) (.forbid 3 7 5 (.system [[0],[2],[3,16,17,18,19,20,7,6],[5],[9,10,11,12],[15]]) (.forbid 3 7 6 (.system [[0,1,2],[3,16,17,18,19,20,21,7,6],[5],[9],[12],[15]]) (certificate_2886_part_1))))))))))))))))))))

noncomputable def certificate_2886_part_3 : FiniteCertificate := .forbid 1 4 2 (.system [[0,1,16,17,4,3],[2],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 1 4 3 (.system [[0,1,16,17,18,4,3],[2],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 1 4 4 (.system [[0,1,16,17,18,19,4,3],[2],[5],[6,7,8,9],[12],[15]]) (.forbid 1 4 5 (.system [[0,1,16,17,18,19,20,4,3],[2],[5],[6,7,8,9],[12],[15]]) (.forbid 1 4 6 (.system [[0,1,16,17,18,19,20,21,4,3],[2],[5],[6],[9],[12],[15]]) (.forbid 1 5 1 (.system [[0,1,16,5],[2],[3],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 1 6 1 (.system [[0,1,16,6,7,8,9,10,11,12,13,14,15],[2],[3],[5]]) (.forbid 1 6 2 (.system [[0,1,16,17,6,7,8,9,10,11,12],[2],[3,4,5],[15]]) (.forbid 1 6 3 (.system [[0,1,16,17,18,6,7,8,9,10,11,12],[2],[3],[5],[15]]) (.forbid 1 6 4 (.system [[0,1,16,17,18,19,6,7,8,9],[2],[3,4,5],[12],[15]]) (.forbid 1 6 5 (.system [[0,1,16,17,18,19,20,6,7,8,9],[2],[3],[5],[12],[15]]) (.forbid 1 6 6 (.system [[0,1,16,17,18,19,20,21,6],[2],[3,4,5],[9],[12],[15]]) (.forbid 1 7 1 (.system [[0,1,16,7,6],[2],[3,4,5],[9,10,11,12,13,14,15]]) (.forbid 1 7 2 (.system [[0,1,16,17,7,6],[2],[3],[5],[9,10,11,12,13,14,15]]) (.forbid 1 7 3 (.system [[0,1,16,17,18,7,6],[2],[3,4,5],[9,10,11,12],[15]]) (.forbid 1 7 4 (.system [[0,1,16,17,18,19,7,6],[2],[3],[5],[9,10,11,12],[15]]) (.forbid 1 7 5 (.system [[0,1,16,17,18,19,20,7,6],[2],[3,4,5],[9],[12],[15]]) (.forbid 1 7 6 (.system [[0,1,16,17,18,19,20,21,7,6],[2],[3],[5],[9],[12],[15]]) (.forbid 2 3 1 (.system [[0,1,2,16,3,4,5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 2 4 1 (.system [[0],[2,16,4,3],[5],[6,7,8,9,10,11,12,13,14,15]]) (certificate_2886_part_2))))))))))))))))))))

noncomputable def certificate_2886_part_4 : FiniteCertificate := .forbid 0 6 2 (.system [[0,16,17,6,7,8,9,10,11,12,13,14,15],[2],[3],[5]]) (.forbid 0 6 3 (.system [[2,1,0,16,17,18,6,7,8,9,10,11,12],[3],[5],[15]]) (.forbid 0 6 4 (.system [[0,16,17,18,19,6,7,8,9,10,11,12],[2],[3],[5],[15]]) (.forbid 0 6 5 (.system [[2,1,0,16,17,18,19,20,6,7,8,9],[3],[5],[12],[15]]) (.forbid 0 6 6 (.system [[0,16,17,18,19,20,21,6,7,8,9],[2],[3],[5],[12],[15]]) (.forbid 0 7 1 (.system [[2,1,0,16,7,8,9,10,11,12,13,14,15],[3],[5],[6]]) (.forbid 0 7 2 (.system [[2,1,0,16,17,7,6],[3],[5],[9,10,11,12,13,14,15]]) (.forbid 0 7 3 (.system [[0,16,17,18,7,6],[2],[3],[5],[9,10,11,12,13,14,15]]) (.forbid 0 7 4 (.system [[2,1,0,16,17,18,19,7,6],[3],[5],[9,10,11,12],[15]]) (.forbid 0 7 5 (.system [[0,16,17,18,19,20,7,6],[2],[3],[5],[9,10,11,12],[15]]) (.forbid 0 7 6 (.system [[2,1,0,16,17,18,19,20,21,7,6],[3],[5],[9],[12],[15]]) (.forbid 0 8 1 (.system [[2,1,0,16,8,7,6],[3],[5],[9,10,11,12,13,14,15]]) (.forbid 1 2 1 (.system [[0,1,16,2],[3],[5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 1 3 1 (.system [[0,1,16,3],[2],[5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3,4,5],[2],[6,7,8,9,10,11,12],[15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3],[2],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3,4,5],[2],[6,7,8,9],[12],[15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3],[2],[5],[6,7,8,9],[12],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,4,5],[2],[6],[9],[12],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3],[2],[5],[6,7,8,9,10,11,12,13,14,15]]) (certificate_2886_part_3))))))))))))))))))))

noncomputable def certificate_2886 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2],[3],[5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2],[3,4,5],[6,7,8,9,10,11,12],[15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2],[3],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2],[3,4,5],[6,7,8,9],[12],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[3],[5],[6,7,8,9],[12],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2],[3,4,5],[6],[9],[12],[15]]) (.forbid 0 3 1 (.system [[2,1,0,16,3,4,5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 3 2 (.system [[0,16,17,3],[2],[5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 3 3 (.system [[2,1,0,16,17,18,3],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 0 3 4 (.system [[0,16,17,18,19,3],[2],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 0 3 5 (.system [[2,1,0,16,17,18,19,20,3],[5],[6,7,8,9],[12],[15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3],[2],[5],[6,7,8,9],[12],[15]]) (.forbid 0 4 1 (.system [[0,16,4,3],[2],[5],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 4 2 (.system [[2,1,0,16,17,4,3],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 0 4 3 (.system [[0,16,17,18,4,3],[2],[5],[6,7,8,9,10,11,12],[15]]) (.forbid 0 4 4 (.system [[2,1,0,16,17,18,19,4,3],[5],[6,7,8,9],[12],[15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[2],[5],[6,7,8,9],[12],[15]]) (.forbid 0 4 6 (.system [[2,1,0,16,17,18,19,20,21,4,3],[5],[6],[9],[12],[15]]) (.forbid 0 5 1 (.system [[2,1,0,16,5,4,3],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 6 1 (.system [[2,1,0,16,6,7,8,9,10,11,12,13,14,15],[3,4,5]]) (certificate_2886_part_4))))))))))))))))))))

noncomputable def certificate_2911_part_1 : FiniteCertificate := .forbid 3 8 5 (.system [[0],[2],[3,17,18,19,20,21,8,7],[5],[9],[12,13,14,15,16]]) (.forbid 3 8 6 (.system [[0],[2],[3,17,18,19,20,21,22,8,7],[5],[9,10,11,12],[16]]) (.forbid 3 10 1 (.system [[0,1,2],[7,6,5,4,3,17,10,11,12,13,14,15,16],[9]]) (.forbid 3 11 1 (.system [[0,1,2],[7,6,5,4,3,17,11,10,9],[12,13,14,15,16]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,17,5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,17,6,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 4 6 2 (.system [[0],[2],[3,4,17,18,6,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 4 6 3 (.system [[0,1,2],[3,4,17,18,19,6,5],[7],[9],[12,13,14,15,16]]) (.forbid 4 6 4 (.system [[0],[2],[3,4,17,18,19,20,6,5],[7],[9],[12,13,14,15,16]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,17,18,19,20,21,6,5],[7],[9,10,11,12],[16]]) (.forbid 4 6 6 (.system [[0,1,2],[3,4,17,18,19,20,21,22,6,5],[7],[9],[12],[16]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,17,7,6,5],[9,10,11,12,13,14,15,16]]) (.forbid 4 8 1 (.system [[0,1,2],[3,4,17,8,7],[5],[9,10,11,12,13,14,15,16]]) (.forbid 4 8 2 (.system [[0],[2],[3,4,17,18,8,7],[5],[9,10,11,12,13,14,15,16]]) (.forbid 4 8 3 (.system [[0,1,2],[3,4,17,18,19,8,7],[5],[9],[12,13,14,15,16]]) (.forbid 4 8 4 (.system [[0],[2],[3,4,17,18,19,20,8,7],[5],[9],[12,13,14,15,16]]) (.forbid 4 8 5 (.system [[0],[2],[3,4,17,18,19,20,21,8,7],[5],[9,10,11,12],[16]]) (.forbid 4 8 6 (.system [[0,1,2],[3,4,17,18,19,20,21,22,8,7],[5],[9],[12],[16]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,17,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 5 8 1 (.system [[0,1,2],[3,4,5,17,8,7],[9,10,11,12,13,14,15,16]]) (certificate_2911_part_0))))))))))))))))))))

noncomputable def certificate_2911_part_2 : FiniteCertificate := .forbid 2 3 1 (.system [[0,1,2,17,3,4,5,6,7,8,9,10,11,12,13,14,15,16]]) (.forbid 2 4 1 (.system [[0,1,2,17,4,3],[5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 2 6 1 (.system [[0,1,2,17,6,5,4,3],[7],[9,10,11,12,13,14,15,16]]) (.forbid 2 8 1 (.system [[0,1,2,17,8,7],[3,4,5],[9,10,11,12,13,14,15,16]]) (.forbid 3 4 1 (.system [[0,1,2],[3,17,4,5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 3 4 2 (.system [[0,1,2],[3,17,18,4,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 3 4 3 (.system [[0],[2],[3,17,18,19,4,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 3 4 4 (.system [[0,1,2],[3,17,18,19,20,4,5],[7],[9],[12,13,14,15,16]]) (.forbid 3 4 5 (.system [[0],[2],[3,17,18,19,20,21,4,5],[7],[9],[12,13,14,15,16]]) (.forbid 3 4 6 (.system [[0],[2],[3,17,18,19,20,21,22,4,5],[7],[9,10,11,12],[16]]) (.forbid 3 6 1 (.system [[0,1,2],[3,17,6,5],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 3 6 2 (.system [[0,1,2],[3,17,18,6,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 3 6 3 (.system [[0],[2],[3,17,18,19,6,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 3 6 4 (.system [[0,1,2],[3,17,18,19,20,6,5],[7],[9],[12,13,14,15,16]]) (.forbid 3 6 5 (.system [[0],[2],[3,17,18,19,20,21,6,5],[7],[9],[12,13,14,15,16]]) (.forbid 3 6 6 (.system [[0],[2],[3,17,18,19,20,21,22,6,5],[7],[9,10,11,12],[16]]) (.forbid 3 8 1 (.system [[0,1,2],[5,4,3,17,8,7],[9,10,11,12,13,14,15,16]]) (.forbid 3 8 2 (.system [[0,1,2],[3,17,18,8,7],[5],[9,10,11,12,13,14,15,16]]) (.forbid 3 8 3 (.system [[0],[2],[3,17,18,19,8,7],[5],[9,10,11,12,13,14,15,16]]) (.forbid 3 8 4 (.system [[0,1,2],[3,17,18,19,20,8,7],[5],[9],[12,13,14,15,16]]) (certificate_2911_part_1))))))))))))))))))))

noncomputable def certificate_2911_part_3 : FiniteCertificate := .forbid 1 4 1 (.system [[0,1,17,4,3],[2],[5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 1 4 2 (.system [[0,1,17,18,4,3],[2],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 1 4 3 (.system [[0,1,17,18,19,4,3],[2],[5,6,7],[9],[12,13,14,15,16]]) (.forbid 1 4 4 (.system [[0,1,17,18,19,20,4,3],[2],[5],[7],[9],[12,13,14,15,16]]) (.forbid 1 4 5 (.system [[0,1,17,18,19,20,21,4,3],[2],[5],[7],[9,10,11,12],[16]]) (.forbid 1 4 6 (.system [[0,1,17,18,19,20,21,22,4,3],[2],[5,6,7],[9],[12],[16]]) (.forbid 1 5 1 (.system [[0,1,17,5,4,3],[2],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 1 6 1 (.system [[0,1,17,6,5,4,3],[2],[7],[9,10,11,12,13,14,15,16]]) (.forbid 1 6 2 (.system [[0,1,17,18,6,5],[2],[3],[7],[9,10,11,12,13,14,15,16]]) (.forbid 1 6 3 (.system [[0,1,17,18,19,6,5,4,3],[2],[7],[9],[12,13,14,15,16]]) (.forbid 1 6 4 (.system [[0,1,17,18,19,20,6,5],[2],[3],[7],[9],[12,13,14,15,16]]) (.forbid 1 6 5 (.system [[0,1,17,18,19,20,21,6,5],[2],[3],[7],[9,10,11,12],[16]]) (.forbid 1 6 6 (.system [[0,1,17,18,19,20,21,22,6,5,4,3],[2],[7],[9],[12],[16]]) (.forbid 1 7 1 (.system [[0,1,17,7,6,5,4,3],[2],[9,10,11,12,13,14,15,16]]) (.forbid 1 8 1 (.system [[0,1,17,8,7],[2],[3,4,5],[9,10,11,12,13,14,15,16]]) (.forbid 1 8 2 (.system [[0,1,17,18,8,7],[2],[3],[5],[9,10,11,12,13,14,15,16]]) (.forbid 1 8 3 (.system [[0,1,17,18,19,8,7],[2],[3,4,5],[9],[12,13,14,15,16]]) (.forbid 1 8 4 (.system [[0,1,17,18,19,20,8,7],[2],[3],[5],[9],[12,13,14,15,16]]) (.forbid 1 8 5 (.system [[0,1,17,18,19,20,21,8,7],[2],[3],[5],[9,10,11,12],[16]]) (.forbid 1 8 6 (.system [[0,1,17,18,19,20,21,22,8,7],[2],[3,4,5],[9],[12],[16]]) (certificate_2911_part_2))))))))))))))))))))

noncomputable def certificate_2911_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[0,17,18,19,6,5],[2],[3],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 6 4 (.system [[2,1,0,17,18,19,20,6,5],[3],[7],[9],[12,13,14,15,16]]) (.forbid 0 6 5 (.system [[0,17,18,19,20,21,6,5],[2],[3],[7],[9],[12,13,14,15,16]]) (.forbid 0 6 6 (.system [[0,17,18,19,20,21,22,6,5],[2],[3],[7],[9,10,11,12],[16]]) (.forbid 0 8 1 (.system [[2,1,0,17,8,7],[3,4,5],[9,10,11,12,13,14,15,16]]) (.forbid 0 8 2 (.system [[2,1,0,17,18,8,7],[3],[5],[9,10,11,12,13,14,15,16]]) (.forbid 0 8 3 (.system [[0,17,18,19,8,7],[2],[3],[5],[9,10,11,12,13,14,15,16]]) (.forbid 0 8 4 (.system [[2,1,0,17,18,19,20,8,7],[3],[5],[9],[12,13,14,15,16]]) (.forbid 0 8 5 (.system [[0,17,18,19,20,21,8,7],[2],[3],[5],[9],[12,13,14,15,16]]) (.forbid 0 8 6 (.system [[0,17,18,19,20,21,22,8,7],[2],[3],[5],[9,10,11,12],[16]]) (.forbid 0 10 1 (.system [[2,1,0,17,10,11,12,13,14,15,16],[3,4,5,6,7],[9]]) (.forbid 0 11 1 (.system [[2,1,0,17,11,10,9],[3,4,5,6,7],[12,13,14,15,16]]) (.forbid 0 13 1 (.system [[2,1,0,17,13,14,15,16],[3,4,5,6,7],[9,10,11,12]]) (.forbid 1 2 1 (.system [[0,1,17,2],[3,4,5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 1 3 1 (.system [[0,1,17,3,4,5,6,7],[2],[9,10,11,12,13,14,15,16]]) (.forbid 1 3 2 (.system [[0,1,17,18,3,4,5],[2],[7],[9,10,11,12,13,14,15,16]]) (.forbid 1 3 3 (.system [[0,1,17,18,19,3],[2],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 1 3 4 (.system [[0,1,17,18,19,20,3,4,5],[2],[7],[9],[12,13,14,15,16]]) (.forbid 1 3 5 (.system [[0,1,17,18,19,20,21,3],[2],[5],[7],[9],[12,13,14,15,16]]) (.forbid 1 3 6 (.system [[0,1,17,18,19,20,21,22,3],[2],[5],[7],[9,10,11,12],[16]]) (certificate_2911_part_3))))))))))))))))))))

noncomputable def certificate_2911 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2],[3,4,5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 0 1 2 (.system [[0,17,18,1,2],[3,4,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1,2],[3],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1,2],[3,4,5],[7],[9],[12,13,14,15,16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2],[3],[5],[7],[9],[12,13,14,15,16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1,2],[3],[5],[7],[9,10,11,12],[16]]) (.forbid 0 3 1 (.system [[2,1,0,17,3,4,5,6,7,8,9,10,11,12,13,14,15,16]]) (.forbid 0 3 2 (.system [[2,1,0,17,18,3,4,5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 3 3 (.system [[2,1,0,17,18,19,3],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 3 4 (.system [[0,17,18,19,20,3],[2],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 3 5 (.system [[2,1,0,17,18,19,20,21,3],[5],[7],[9],[12,13,14,15,16]]) (.forbid 0 3 6 (.system [[0,17,18,19,20,21,22,3],[2],[5],[7],[9],[12,13,14,15,16]]) (.forbid 0 4 1 (.system [[2,1,0,17,4,3],[5,6,7],[9,10,11,12,13,14,15,16]]) (.forbid 0 4 2 (.system [[2,1,0,17,18,4,3],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 4 3 (.system [[0,17,18,19,4,3],[2],[5],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 4 4 (.system [[2,1,0,17,18,19,20,4,3],[5],[7],[9],[12,13,14,15,16]]) (.forbid 0 4 5 (.system [[0,17,18,19,20,21,4,3],[2],[5],[7],[9],[12,13,14,15,16]]) (.forbid 0 4 6 (.system [[0,17,18,19,20,21,22,4,3],[2],[5],[7],[9,10,11,12],[16]]) (.forbid 0 6 1 (.system [[2,1,0,17,6,5,4,3],[7],[9,10,11,12,13,14,15,16]]) (.forbid 0 6 2 (.system [[2,1,0,17,18,6,5],[3],[7],[9,10,11,12,13,14,15,16]]) (certificate_2911_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates092
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2912_part_1 : FiniteCertificate := .forbid 3 10 1 (.system [[0,1,2],[9,8,7,6,5,4,3,16,10,11,12,13],[15]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,16,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,16,6,5],[7,8,9,10,11,12,13],[15]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,16,17,6,5],[7],[9,10,11,12,13],[15]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,16,17,18,6,5],[7],[9,10,11,12,13],[15]]) (.forbid 4 6 4 (.system [[0],[2],[3,4,16,17,18,19,6,5],[7],[9,10,11,12,13],[15]]) (.forbid 4 6 5 (.system [[0,1,2],[3,4,16,17,18,19,20,6,5],[7],[9],[13],[15]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,16,17,18,19,20,21,6,5],[7],[9],[13],[15]]) (.forbid 4 8 1 (.system [[0,1,2],[3,4,16,8,7,6,5],[9,10,11,12,13],[15]]) (.forbid 4 8 2 (.system [[0,1,2],[3,4,16,17,8,7],[5],[9,10,11,12,13],[15]]) (.forbid 4 8 3 (.system [[0],[2],[3,4,16,17,18,8,7],[5],[9,10,11,12,13],[15]]) (.forbid 4 8 4 (.system [[0],[2],[3,4,16,17,18,19,8,7],[5],[9,10,11,12,13],[15]]) (.forbid 4 8 5 (.system [[0,1,2],[3,4,16,17,18,19,20,8,7],[5],[9],[13],[15]]) (.forbid 4 8 6 (.system [[0],[2],[3,4,16,17,18,19,20,21,8,7],[5],[9],[13],[15]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,16,6,7,8,9,10,11,12,13],[15]]) (.forbid 5 8 1 (.system [[0,1,2],[3,4,5,16,8,7],[9,10,11,12,13,14,15]]) (.forbid 6 8 1 (.system [[0,1,2],[3,4,5,6,16,8,7],[9,10,11,12,13],[15]]) (.forbid 6 8 2 (.system [[0,1,2],[3],[5,6,16,17,8,7],[9,10,11,12,13],[15]]) (.forbid 6 8 3 (.system [[0],[2],[3],[5,6,16,17,18,8,7],[9,10,11,12,13],[15]]) (.forbid 6 8 4 (.system [[0],[2],[3],[5,6,16,17,18,19,8,7],[9,10,11,12,13],[15]]) (certificate_2912_part_0))))))))))))))))))))

noncomputable def certificate_2912_part_2 : FiniteCertificate := .forbid 2 6 1 (.system [[0,1,2,16,6,5,4,3],[7,8,9,10,11,12,13],[15]]) (.forbid 2 8 1 (.system [[0,1,2,16,8,7,6,5,4,3],[9,10,11,12,13],[15]]) (.forbid 3 4 1 (.system [[0,1,2],[3,16,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 3 4 2 (.system [[0,1,2],[3,16,17,4,5,6,7],[9,10,11,12,13],[15]]) (.forbid 3 4 3 (.system [[0,1,2],[3,16,17,18,4,5],[7],[9,10,11,12,13],[15]]) (.forbid 3 4 4 (.system [[0],[2],[3,16,17,18,19,4,5],[7],[9,10,11,12,13],[15]]) (.forbid 3 4 5 (.system [[0],[2],[3,16,17,18,19,20,4,5],[7],[9,10,11,12,13],[15]]) (.forbid 3 4 6 (.system [[0,1,2],[3,16,17,18,19,20,21,4,5],[7],[9],[13],[15]]) (.forbid 3 6 1 (.system [[0,1,2],[3,16,6,5],[7,8,9,10,11,12,13,14,15]]) (.forbid 3 6 2 (.system [[0,1,2],[3,16,17,6,5],[7,8,9,10,11,12,13],[15]]) (.forbid 3 6 3 (.system [[0,1,2],[3,16,17,18,6,5],[7],[9,10,11,12,13],[15]]) (.forbid 3 6 4 (.system [[0],[2],[3,16,17,18,19,6,5],[7],[9,10,11,12,13],[15]]) (.forbid 3 6 5 (.system [[0],[2],[3,16,17,18,19,20,6,5],[7],[9,10,11,12,13],[15]]) (.forbid 3 6 6 (.system [[0,1,2],[3,16,17,18,19,20,21,6,5],[7],[9],[13],[15]]) (.forbid 3 8 1 (.system [[0,1,2],[5,4,3,16,8,7],[9,10,11,12,13,14,15]]) (.forbid 3 8 2 (.system [[0,1,2],[5,4,3,16,17,8,7],[9,10,11,12,13],[15]]) (.forbid 3 8 3 (.system [[0,1,2],[3,16,17,18,8,7],[5],[9,10,11,12,13],[15]]) (.forbid 3 8 4 (.system [[0],[2],[3,16,17,18,19,8,7],[5],[9,10,11,12,13],[15]]) (.forbid 3 8 5 (.system [[0],[2],[3,16,17,18,19,20,8,7],[5],[9,10,11,12,13],[15]]) (.forbid 3 8 6 (.system [[0,1,2],[3,16,17,18,19,20,21,8,7],[5],[9],[13],[15]]) (certificate_2912_part_1))))))))))))))))))))

noncomputable def certificate_2912_part_3 : FiniteCertificate := .forbid 1 4 2 (.system [[0,1,16,17,4,3],[2],[5,6,7],[9,10,11,12,13],[15]]) (.forbid 1 4 3 (.system [[0,1,16,17,18,4,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 1 4 4 (.system [[0,1,16,17,18,19,4,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 1 4 5 (.system [[0,1,16,17,18,19,20,4,3],[2],[5,6,7],[9],[13],[15]]) (.forbid 1 4 6 (.system [[0,1,16,17,18,19,20,21,4,3],[2],[5],[7],[9],[13],[15]]) (.forbid 1 5 1 (.system [[0,1,16,5,4,3],[2],[7,8,9,10,11,12,13,14,15]]) (.forbid 1 6 1 (.system [[0,1,16,6,5,4,3],[2],[7,8,9,10,11,12,13],[15]]) (.forbid 1 6 2 (.system [[0,1,16,17,6,5,4,3],[2],[7],[9,10,11,12,13],[15]]) (.forbid 1 6 3 (.system [[0,1,16,17,18,6,5],[2],[3],[7],[9,10,11,12,13],[15]]) (.forbid 1 6 4 (.system [[0,1,16,17,18,19,6,5],[2],[3],[7],[9,10,11,12,13],[15]]) (.forbid 1 6 5 (.system [[0,1,16,17,18,19,20,6,5,4,3],[2],[7],[9],[13],[15]]) (.forbid 1 6 6 (.system [[0,1,16,17,18,19,20,21,6,5],[2],[3],[7],[9],[13],[15]]) (.forbid 1 8 1 (.system [[0,1,16,8,7,6,5,4,3],[2],[9,10,11,12,13],[15]]) (.forbid 1 8 2 (.system [[0,1,16,17,8,7],[2],[3,4,5],[9,10,11,12,13],[15]]) (.forbid 1 8 3 (.system [[0,1,16,17,18,8,7],[2],[3],[5],[9,10,11,12,13],[15]]) (.forbid 1 8 4 (.system [[0,1,16,17,18,19,8,7],[2],[3],[5],[9,10,11,12,13],[15]]) (.forbid 1 8 5 (.system [[0,1,16,17,18,19,20,8,7],[2],[3,4,5],[9],[13],[15]]) (.forbid 1 8 6 (.system [[0,1,16,17,18,19,20,21,8,7],[2],[3],[5],[9],[13],[15]]) (.forbid 2 3 1 (.system [[0,1,2,16,3,4,5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 2 4 1 (.system [[0,1,2,16,4,3],[5,6,7,8,9,10,11,12,13],[15]]) (certificate_2912_part_2))))))))))))))))))))

noncomputable def certificate_2912_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,16,17,18,6,5],[3],[7],[9,10,11,12,13],[15]]) (.forbid 0 6 4 (.system [[0,16,17,18,19,6,5],[2],[3],[7],[9,10,11,12,13],[15]]) (.forbid 0 6 5 (.system [[0,16,17,18,19,20,6,5],[2],[3],[7],[9,10,11,12,13],[15]]) (.forbid 0 6 6 (.system [[2,1,0,16,17,18,19,20,21,6,5],[3],[7],[9],[13],[15]]) (.forbid 0 8 1 (.system [[2,1,0,16,8,7,6,5,4,3],[9,10,11,12,13],[15]]) (.forbid 0 8 2 (.system [[2,1,0,16,17,8,7],[3,4,5],[9,10,11,12,13],[15]]) (.forbid 0 8 3 (.system [[2,1,0,16,17,18,8,7],[3],[5],[9,10,11,12,13],[15]]) (.forbid 0 8 4 (.system [[0,16,17,18,19,8,7],[2],[3],[5],[9,10,11,12,13],[15]]) (.forbid 0 8 5 (.system [[0,16,17,18,19,20,8,7],[2],[3],[5],[9,10,11,12,13],[15]]) (.forbid 0 8 6 (.system [[2,1,0,16,17,18,19,20,21,8,7],[3],[5],[9],[13],[15]]) (.forbid 0 10 1 (.system [[2,1,0,16,10,11,12,13],[3,4,5,6,7,8,9],[15]]) (.forbid 0 12 1 (.system [[2,1,0,16,12,11,10,9,8,7,6,5,4,3],[13],[15]]) (.forbid 1 2 1 (.system [[0,1,16,2],[3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 1 3 1 (.system [[0,1,16,3,4,5,6,7,8,9,10,11,12,13],[2],[15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3,4,5,6,7],[2],[9,10,11,12,13],[15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3,4,5],[2],[7],[9,10,11,12,13],[15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,4,5],[2],[7],[9],[13],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3],[2],[5,6,7,8,9,10,11,12,13],[15]]) (certificate_2912_part_3))))))))))))))))))))

noncomputable def certificate_2912 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2],[3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2],[3,4,5,6,7],[9,10,11,12,13],[15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2],[3,4,5],[7],[9,10,11,12,13],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2],[3],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[3],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2],[3,4,5],[7],[9],[13],[15]]) (.forbid 0 3 1 (.system [[2,1,0,16,3,4,5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 3 2 (.system [[2,1,0,16,17,3,4,5,6,7],[9,10,11,12,13],[15]]) (.forbid 0 3 3 (.system [[2,1,0,16,17,18,3,4,5],[7],[9,10,11,12,13],[15]]) (.forbid 0 3 4 (.system [[2,1,0,16,17,18,19,3],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 3 5 (.system [[0,16,17,18,19,20,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 4 1 (.system [[2,1,0,16,4,3],[5,6,7,8,9,10,11,12,13],[15]]) (.forbid 0 4 2 (.system [[2,1,0,16,17,4,3],[5,6,7],[9,10,11,12,13],[15]]) (.forbid 0 4 3 (.system [[2,1,0,16,17,18,4,3],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 4 4 (.system [[0,16,17,18,19,4,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[2],[5],[7],[9,10,11,12,13],[15]]) (.forbid 0 4 6 (.system [[2,1,0,16,17,18,19,20,21,4,3],[5],[7],[9],[13],[15]]) (.forbid 0 6 1 (.system [[2,1,0,16,6,5,4,3],[7,8,9,10,11,12,13],[15]]) (.forbid 0 6 2 (.system [[2,1,0,16,17,6,5,4,3],[7],[9,10,11,12,13],[15]]) (certificate_2912_part_4))))))))))))))))))))

noncomputable def certificate_2916_part_1 : FiniteCertificate := .forbid 3 9 1 (.system [[0,1,2],[5,4,3,16,9,8,7],[10],[11,12,13,14,15]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,16,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 4 6 1 (.system [[0],[2],[3,4,16,6,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,16,17,6,5],[7],[10],[11,12,13,14,15]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,16,17,18,6,5],[7],[10],[11,12,13,14,15]]) (.forbid 4 6 4 (.system [[0],[2],[3,4,16,17,18,19,6,5],[7,8,9,10],[11],[15]]) (.forbid 4 6 5 (.system [[0,1,2],[3,4,16,17,18,19,20,6,5],[7],[10],[11],[15]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,16,17,18,19,20,21,6,5],[7],[10],[11],[15]]) (.forbid 4 8 1 (.system [[0,1,2],[3,4,16,8,7,6,5],[10],[11,12,13,14,15]]) (.forbid 4 8 2 (.system [[0,1,2],[3,4,16,17,8,7],[5],[10],[11,12,13,14,15]]) (.forbid 4 8 3 (.system [[0],[2],[3,4,16,17,18,8,7],[5],[10],[11,12,13,14,15]]) (.forbid 4 8 4 (.system [[0],[2],[3,4,16,17,18,19,8,7],[5],[10],[11,12,13,14,15]]) (.forbid 4 8 5 (.system [[0,1,2],[3,4,16,17,18,19,20,8,7],[5],[10],[11],[15]]) (.forbid 4 8 6 (.system [[0],[2],[3,4,16,17,18,19,20,21,8,7],[5],[10],[11],[15]]) (.forbid 5 6 1 (.system [[0,1,2],[3],[5,16,6,7,8,9,10],[11,12,13,14,15]]) (.forbid 5 8 1 (.system [[0,1,2],[3,4,5,16,8,9,10],[7],[11,12,13,14,15]]) (.forbid 6 8 1 (.system [[0,1,2],[3,4,5,6,16,8,7],[10],[11,12,13,14,15]]) (.forbid 6 8 2 (.system [[0,1,2],[3],[5,6,16,17,8,7],[10],[11,12,13,14,15]]) (.forbid 6 8 3 (.system [[0],[2],[3],[5,6,16,17,18,8,7],[10],[11,12,13,14,15]]) (.forbid 6 8 4 (.system [[0],[2],[3],[5,6,16,17,18,19,8,7],[10],[11,12,13,14,15]]) (certificate_2916_part_0))))))))))))))))))))

noncomputable def certificate_2916_part_2 : FiniteCertificate := .forbid 2 6 1 (.system [[0,1,2,16,6,5],[3],[7,8,9,10],[11,12,13,14,15]]) (.forbid 2 8 1 (.system [[0,1,2,16,8,9,10],[3,4,5],[7],[11,12,13,14,15]]) (.forbid 3 4 1 (.system [[0,1,2],[3,16,4,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 3 4 2 (.system [[0],[2],[3,16,17,4,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 3 4 3 (.system [[0,1,2],[3,16,17,18,4,5],[7],[10],[11,12,13,14,15]]) (.forbid 3 4 4 (.system [[0],[2],[3,16,17,18,19,4,5],[7],[10],[11,12,13,14,15]]) (.forbid 3 4 5 (.system [[0],[2],[3,16,17,18,19,20,4,5],[7,8,9,10],[11],[15]]) (.forbid 3 4 6 (.system [[0,1,2],[3,16,17,18,19,20,21,4,5],[7],[10],[11],[15]]) (.forbid 3 6 1 (.system [[0,1,2],[3,16,6,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 3 6 2 (.system [[0],[2],[3,16,17,6,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 3 6 3 (.system [[0,1,2],[3,16,17,18,6,5],[7],[10],[11,12,13,14,15]]) (.forbid 3 6 4 (.system [[0],[2],[3,16,17,18,19,6,5],[7],[10],[11,12,13,14,15]]) (.forbid 3 6 5 (.system [[0],[2],[3,16,17,18,19,20,6,5],[7,8,9,10],[11],[15]]) (.forbid 3 6 6 (.system [[0,1,2],[3,16,17,18,19,20,21,6,5],[7],[10],[11],[15]]) (.forbid 3 8 1 (.system [[0,1,2],[5,4,3,16,8,9,10],[7],[11,12,13,14,15]]) (.forbid 3 8 2 (.system [[0,1,2],[5,4,3,16,17,8,7],[10],[11,12,13,14,15]]) (.forbid 3 8 3 (.system [[0,1,2],[3,16,17,18,8,7],[5],[10],[11,12,13,14,15]]) (.forbid 3 8 4 (.system [[0],[2],[3,16,17,18,19,8,7],[5],[10],[11,12,13,14,15]]) (.forbid 3 8 5 (.system [[0],[2],[3,16,17,18,19,20,8,7],[5],[10],[11,12,13,14,15]]) (.forbid 3 8 6 (.system [[0,1,2],[3,16,17,18,19,20,21,8,7],[5],[10],[11],[15]]) (certificate_2916_part_1))))))))))))))))))))

noncomputable def certificate_2916_part_3 : FiniteCertificate := .forbid 1 4 2 (.system [[0,1,16,17,4,3],[2],[5,6,7],[10],[11,12,13,14,15]]) (.forbid 1 4 3 (.system [[0,1,16,17,18,4,3],[2],[5],[7],[10],[11,12,13,14,15]]) (.forbid 1 4 4 (.system [[0,1,16,17,18,19,4,3],[2],[5],[7,8,9,10],[11],[15]]) (.forbid 1 4 5 (.system [[0,1,16,17,18,19,20,4,3],[2],[5,6,7],[10],[11],[15]]) (.forbid 1 4 6 (.system [[0,1,16,17,18,19,20,21,4,3],[2],[5],[7],[10],[11],[15]]) (.forbid 1 5 1 (.system [[0,1,16,5,4,3],[2],[7,8,9,10],[11,12,13,14,15]]) (.forbid 1 6 1 (.system [[0,1,16,6,5],[2],[3],[7,8,9,10],[11,12,13,14,15]]) (.forbid 1 6 2 (.system [[0,1,16,17,6,5,4,3],[2],[7],[10],[11,12,13,14,15]]) (.forbid 1 6 3 (.system [[0,1,16,17,18,6,5],[2],[3],[7],[10],[11,12,13,14,15]]) (.forbid 1 6 4 (.system [[0,1,16,17,18,19,6,5],[2],[3],[7,8,9,10],[11],[15]]) (.forbid 1 6 5 (.system [[0,1,16,17,18,19,20,6,5,4,3],[2],[7],[10],[11],[15]]) (.forbid 1 6 6 (.system [[0,1,16,17,18,19,20,21,6,5],[2],[3],[7],[10],[11],[15]]) (.forbid 1 8 1 (.system [[0,1,16,8,7,6,5,4,3],[2],[10],[11,12,13,14,15]]) (.forbid 1 8 2 (.system [[0,1,16,17,8,7],[2],[3,4,5],[10],[11,12,13,14,15]]) (.forbid 1 8 3 (.system [[0,1,16,17,18,8,7],[2],[3],[5],[10],[11,12,13,14,15]]) (.forbid 1 8 4 (.system [[0,1,16,17,18,19,8,7],[2],[3],[5],[10],[11,12,13,14,15]]) (.forbid 1 8 5 (.system [[0,1,16,17,18,19,20,8,7],[2],[3,4,5],[10],[11],[15]]) (.forbid 1 8 6 (.system [[0,1,16,17,18,19,20,21,8,7],[2],[3],[5],[10],[11],[15]]) (.forbid 2 3 1 (.system [[0,1,2,16,3,4,5,6,7,8,9,10],[11,12,13,14,15]]) (.forbid 2 4 1 (.system [[0,1,2,16,4,3],[5],[7,8,9,10],[11,12,13,14,15]]) (certificate_2916_part_2))))))))))))))))))))

noncomputable def certificate_2916_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,16,17,18,6,5],[3],[7],[10],[11,12,13,14,15]]) (.forbid 0 6 4 (.system [[0,16,17,18,19,6,5],[2],[3],[7],[10],[11,12,13,14,15]]) (.forbid 0 6 5 (.system [[0,16,17,18,19,20,6,5],[2],[3],[7,8,9,10],[11],[15]]) (.forbid 0 6 6 (.system [[2,1,0,16,17,18,19,20,21,6,5],[3],[7],[10],[11],[15]]) (.forbid 0 8 1 (.system [[2,1,0,16,8,9,10],[3,4,5],[7],[11,12,13,14,15]]) (.forbid 0 8 2 (.system [[2,1,0,16,17,8,7],[3,4,5],[10],[11,12,13,14,15]]) (.forbid 0 8 3 (.system [[2,1,0,16,17,18,8,7],[3],[5],[10],[11,12,13,14,15]]) (.forbid 0 8 4 (.system [[0,16,17,18,19,8,7],[2],[3],[5],[10],[11,12,13,14,15]]) (.forbid 0 8 5 (.system [[0,16,17,18,19,20,8,7],[2],[3],[5],[10],[11,12,13,14,15]]) (.forbid 0 8 6 (.system [[2,1,0,16,17,18,19,20,21,8,7],[3],[5],[10],[11],[15]]) (.forbid 0 9 1 (.system [[2,1,0,16,9,8,7],[3,4,5],[10],[11,12,13,14,15]]) (.forbid 0 10 1 (.system [[2,1,0,16,10,9,8,7,6,5,4,3],[11,12,13,14,15]]) (.forbid 1 2 1 (.system [[0,1,16,2],[3,4,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 1 3 1 (.system [[0,1,16,3,4,5],[2],[7,8,9,10],[11,12,13,14,15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3],[2],[5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3,4,5],[2],[7],[10],[11,12,13,14,15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3],[2],[5],[7],[10],[11,12,13,14,15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3],[2],[5],[7,8,9,10],[11],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,4,5],[2],[7],[10],[11],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3],[2],[5],[7,8,9,10],[11,12,13,14,15]]) (certificate_2916_part_3))))))))))))))))))))

noncomputable def certificate_2916 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2],[3,4,5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2],[3],[5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2],[3,4,5],[7],[10],[11,12,13,14,15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2],[3],[5],[7],[10],[11,12,13,14,15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[3],[5],[7,8,9,10],[11],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2],[3,4,5],[7],[10],[11],[15]]) (.forbid 0 3 1 (.system [[2,1,0,16,3,4,5,6,7,8,9,10],[11,12,13,14,15]]) (.forbid 0 3 2 (.system [[2,1,0,16,17,3],[5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 3 3 (.system [[0,16,17,18,3],[2],[5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 3 4 (.system [[2,1,0,16,17,18,19,3],[5],[7],[10],[11,12,13,14,15]]) (.forbid 0 3 5 (.system [[0,16,17,18,19,20,3],[2],[5],[7],[10],[11,12,13,14,15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3],[2],[5],[7,8,9,10],[11],[15]]) (.forbid 0 4 1 (.system [[2,1,0,16,4,3],[5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 4 2 (.system [[0,16,17,4,3],[2],[5],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 4 3 (.system [[2,1,0,16,17,18,4,3],[5],[7],[10],[11,12,13,14,15]]) (.forbid 0 4 4 (.system [[0,16,17,18,19,4,3],[2],[5],[7],[10],[11,12,13,14,15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[2],[5],[7,8,9,10],[11],[15]]) (.forbid 0 4 6 (.system [[2,1,0,16,17,18,19,20,21,4,3],[5],[7],[10],[11],[15]]) (.forbid 0 6 1 (.system [[2,1,0,16,6,5],[3],[7,8,9,10],[11,12,13,14,15]]) (.forbid 0 6 2 (.system [[0,16,17,6,5],[2],[3],[7,8,9,10],[11,12,13,14,15]]) (certificate_2916_part_4))))))))))))))))))))

noncomputable def certificate_2939_part_3 : FiniteCertificate := .forbid 1 4 2 (.system [[0,1,16,17,4,3],[2],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 1 4 3 (.system [[0,1,16,17,18,4,3],[2],[5,6,7,8,9,10],[12],[15]]) (.forbid 1 4 4 (.system [[0,1,16,17,18,19,4,3],[2],[5,6,7,8],[10],[12],[15]]) (.forbid 1 4 5 (.system [[0,1,16,17,18,19,20,4,3],[2],[5,6,7,8],[10],[12],[15]]) (.forbid 1 4 6 (.system [[0,1,16,17,18,19,20,21,4,3],[2],[5],[8],[10],[12],[15]]) (.forbid 1 5 1 (.system [[0,1,16,5,6,7,8,9,10,11,12,13,14,15],[2],[3]]) (.forbid 1 6 1 (.system [[0,1,16,6,5,4,3],[2],[8,9,10,11,12,13,14,15]]) (.forbid 1 6 2 (.system [[0,1,16,17,6,5,4,3],[2],[8,9,10],[12,13,14,15]]) (.forbid 1 6 3 (.system [[0,1,16,17,18,6,5,4,3],[2],[8],[10],[12,13,14,15]]) (.forbid 1 6 4 (.system [[0,1,16,17,18,19,6,5],[2],[3],[8],[10],[12,13,14,15]]) (.forbid 1 6 5 (.system [[0,1,16,17,18,19,20,6,5,4,3],[2],[8],[10],[12],[15]]) (.forbid 1 6 6 (.system [[0,1,16,17,18,19,20,21,6,5],[2],[3],[8],[10],[12],[15]]) (.forbid 1 7 1 (.system [[0,1,16,7,6,5,4,3],[2],[8,9,10],[12,13,14,15]]) (.forbid 1 7 2 (.system [[0,1,16,17,7,6,5,4,3],[2],[8],[10],[12,13,14,15]]) (.forbid 1 7 3 (.system [[0,1,16,17,18,7,6,5],[2],[3],[8],[10],[12,13,14,15]]) (.forbid 1 7 4 (.system [[0,1,16,17,18,19,7,6,5,4,3],[2],[8],[10],[12],[15]]) (.forbid 1 7 5 (.system [[0,1,16,17,18,19,20,7,6,5],[2],[3],[8],[10],[12],[15]]) (.forbid 1 7 6 (.system [[0,1,16,17,18,19,20,21,7,6,5],[2],[3],[8],[10],[12],[15]]) (.forbid 2 3 1 (.system [[0,1,2,16,3,4,5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 2 4 1 (.system [[0,1,2,16,4,3],[5,6,7,8,9,10],[12,13,14,15]]) (certificate_2939_part_2))))))))))))))))))))

noncomputable def certificate_2939_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,16,17,18,6,5,4,3],[8],[10],[12,13,14,15]]) (.forbid 0 6 4 (.system [[2,1,0,16,17,18,19,6,5],[3],[8],[10],[12,13,14,15]]) (.forbid 0 6 5 (.system [[0,16,17,18,19,20,6,5],[2],[3],[8],[10],[12,13,14,15]]) (.forbid 0 6 6 (.system [[2,1,0,16,17,18,19,20,21,6,5],[3],[8],[10],[12],[15]]) (.forbid 0 7 1 (.system [[2,1,0,16,7,6,5,4,3],[8,9,10],[12,13,14,15]]) (.forbid 0 7 2 (.system [[2,1,0,16,17,7,6,5,4,3],[8],[10],[12,13,14,15]]) (.forbid 0 7 3 (.system [[2,1,0,16,17,18,7,6,5],[3],[8],[10],[12,13,14,15]]) (.forbid 0 7 4 (.system [[0,16,17,18,19,7,6,5],[2],[3],[8],[10],[12,13,14,15]]) (.forbid 0 7 5 (.system [[2,1,0,16,17,18,19,20,7,6,5],[3],[8],[10],[12],[15]]) (.forbid 0 7 6 (.system [[0,16,17,18,19,20,21,7,6,5],[2],[3],[8],[10],[12],[15]]) (.forbid 0 9 1 (.system [[2,1,0,16,9,8,7,6,5,4,3],[10],[12,13,14,15]]) (.forbid 0 11 1 (.system [[2,1,0,16,11,10],[3,4,5,6,7,8],[12,13,14,15]]) (.forbid 1 2 1 (.system [[0,1,16,2],[3,4,5,6,7,8,9,10],[12,13,14,15]]) (.forbid 1 3 1 (.system [[0,1,16,3,4,5,6,7,8,9,10],[2],[12,13,14,15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3,4,5,6,7,8],[2],[10],[12,13,14,15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3],[2],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3,4,5,6,7,8],[2],[10],[12],[15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3],[2],[5,6,7,8],[10],[12],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,4,5],[2],[8],[10],[12],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3],[2],[5,6,7,8,9,10],[12,13,14,15]]) (certificate_2939_part_3))))))))))))))))))))

noncomputable def certificate_2939 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2],[3,4,5,6,7,8,9,10],[12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2],[3,4,5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2],[3],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2],[3,4,5,6,7,8],[10],[12],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[3],[5,6,7,8],[10],[12],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2],[3,4,5],[8],[10],[12],[15]]) (.forbid 0 3 1 (.system [[2,1,0,16,3,4,5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 3 2 (.system [[2,1,0,16,17,3,4,5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 3 3 (.system [[2,1,0,16,17,18,3],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 3 4 (.system [[0,16,17,18,19,3],[2],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 3 5 (.system [[2,1,0,16,17,18,19,20,3],[5,6,7,8],[10],[12],[15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3],[2],[5,6,7,8],[10],[12],[15]]) (.forbid 0 4 1 (.system [[2,1,0,16,4,3],[5,6,7,8,9,10],[12,13,14,15]]) (.forbid 0 4 2 (.system [[2,1,0,16,17,4,3],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 4 3 (.system [[0,16,17,18,4,3],[2],[5,6,7,8],[10],[12,13,14,15]]) (.forbid 0 4 4 (.system [[2,1,0,16,17,18,19,4,3],[5,6,7,8],[10],[12],[15]]) (.forbid 0 4 5 (.system [[0,16,17,18,19,20,4,3],[2],[5,6,7,8],[10],[12],[15]]) (.forbid 0 4 6 (.system [[2,1,0,16,17,18,19,20,21,4,3],[5],[8],[10],[12],[15]]) (.forbid 0 6 1 (.system [[2,1,0,16,6,7,8,9,10],[3,4,5],[12,13,14,15]]) (.forbid 0 6 2 (.system [[2,1,0,16,17,6,5,4,3],[8,9,10],[12,13,14,15]]) (certificate_2939_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates093
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2964 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2],[3,4,5,6,7,8,9,10],[12,13,14,15,16]]) (.forbid 0 1 2 (.system [[0,17,18,1,2],[3,4,5,6,7,8],[10],[12,13,14,15,16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1,2],[3,4,5,6],[8],[10],[12,13,14,15,16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1,2],[3,4,5,6],[8],[10],[12,13,14,15,16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2],[3],[6],[8],[10],[12,13,14,15,16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1,2],[3,4,5,6],[8],[10],[12],[16]]) (.forbid 0 3 1 (.system [[2,1,0,17,3,4,5,6,7,8,9,10,11,12,13,14,15,16]]) (.forbid 0 3 2 (.system [[2,1,0,17,18,3,4,5,6,7,8],[10],[12,13,14,15,16]]) (.forbid 0 3 3 (.system [[2,1,0,17,18,19,3,4,5,6],[8],[10],[12,13,14,15,16]]) (.forbid 0 3 4 (.system [[0,17,18,19,20,3,4,5,6],[2],[8],[10],[12,13,14,15,16]]) (.forbid 0 3 5 (.system [[2,1,0,17,18,19,20,21,3],[6],[8],[10],[12,13,14,15,16]]) (.forbid 0 3 6 (.system [[0,17,18,19,20,21,22,3],[2],[6],[8],[10],[12,13,14,15,16]]) (.forbid 0 4 1 (.system [[2,1,0,17,4,5,6,7,8,9,10],[3],[12,13,14,15,16]]) (.forbid 0 4 2 (.system [[2,1,0,17,18,4,3],[6,7,8,9,10],[12,13,14,15,16]]) (.forbid 0 4 3 (.system [[2,1,0,17,18,19,4,3],[6,7,8],[10],[12,13,14,15,16]]) (.forbid 0 4 4 (.system [[2,1,0,17,18,19,20,4,3],[6],[8],[10],[12,13,14,15,16]]) (.forbid 0 4 5 (.system [[0,17,18,19,20,21,4,3],[2],[6],[8],[10],[12,13,14,15,16]]) (.forbid 0 4 6 (.system [[0,17,18,19,20,21,22,4,3],[2],[6],[8],[10],[12,13,14,15,16]]) (.forbid 0 5 1 (.system [[2,1,0,17,5,4,3],[6,7,8,9,10],[12,13,14,15,16]]) (.forbid 0 7 1 (.system [[2,1,0,17,7,6,5,4,3],[8,9,10],[12,13,14,15,16]]) (certificate_2964_part_4))))))))))))))))))))

noncomputable def certificate_2971_part_1 : FiniteCertificate := .forbid 4 5 1 (.system [[0,1,2,3,4,16,5,6,7,8,9],[10,11,12,13,14,15]]) (.forbid 4 6 1 (.system [[0,1,2,3,4,16,6,5],[7],[9],[10,11,12,13,14,15]]) (.forbid 4 8 1 (.system [[0,1,2,3,4,16,8,7],[5],[9],[10,11,12,13,14,15]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,16,6,7],[9],[10,11,12,13,14,15]]) (.forbid 5 6 2 (.system [[0,1,2],[4],[5,16,17,6,7],[9],[10,11,12,13,14,15]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,16,17,18,6,7],[9],[10,11,12,13,14,15]]) (.forbid 5 6 4 (.system [[0],[2],[4],[5,16,17,18,19,6,7],[9],[10,11,12,13,14,15]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,16,17,18,19,20,6,7],[9],[10,11,12,13,14,15]]) (.forbid 5 6 6 (.system [[0,1,2],[4],[5,16,17,18,19,20,21,6,7],[9],[10],[15]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[5,16,8,7],[9],[10,11,12,13,14,15]]) (.forbid 5 8 2 (.system [[0,1,2],[4],[5,16,17,8,7],[9],[10,11,12,13,14,15]]) (.forbid 5 8 3 (.system [[0],[2],[4],[5,16,17,18,8,7],[9],[10,11,12,13,14,15]]) (.forbid 5 8 4 (.system [[0],[2],[4],[5,16,17,18,19,8,7],[9],[10,11,12,13,14,15]]) (.forbid 5 8 5 (.system [[0],[2],[4],[5,16,17,18,19,20,8,7],[9],[10,11,12,13,14,15]]) (.forbid 5 8 6 (.system [[0,1,2],[4],[5,16,17,18,19,20,21,8,7],[9],[10],[15]]) (.forbid 5 10 1 (.system [[0,1,2,3,4],[9,8,7,6,5,16,10,11,12,13,14,15]]) (.forbid 6 8 1 (.system [[0,1,2],[4],[5,6,16,8,7],[9],[10,11,12,13,14,15]]) (.forbid 6 8 2 (.system [[0],[2],[4],[5,6,16,17,8,7],[9],[10,11,12,13,14,15]]) (.forbid 6 8 3 (.system [[0],[2],[4],[5,6,16,17,18,8,7],[9],[10,11,12,13,14,15]]) (.forbid 6 8 4 (.system [[0],[2],[4],[5,6,16,17,18,19,8,7],[9],[10,11,12,13,14,15]]) (certificate_2971_part_0))))))))))))))))))))

noncomputable def certificate_2971_part_2 : FiniteCertificate := .forbid 2 8 1 (.system [[0,1,2,16,8,7,6,5],[4],[9],[10,11,12,13,14,15]]) (.forbid 3 4 1 (.system [[0,1,2,3,16,4],[5,6,7],[9],[10,11,12,13,14,15]]) (.forbid 3 5 1 (.system [[0,1,2,3,16,5,6,7],[4],[9],[10,11,12,13,14,15]]) (.forbid 3 5 2 (.system [[0,1,2,3,16,17,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 5 3 (.system [[0],[2,3,16,17,18,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 5 4 (.system [[0],[2,3,16,17,18,19,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 5 5 (.system [[0],[2,3,16,17,18,19,20,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 5 6 (.system [[0,1,2,3,16,17,18,19,20,21,5],[4],[7],[9],[10],[15]]) (.forbid 3 6 1 (.system [[0,1,2,3,16,6,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 6 2 (.system [[0],[2,3,16,17,6,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 6 3 (.system [[0],[2,3,16,17,18,6,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 6 4 (.system [[0],[2,3,16,17,18,19,6,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 3 6 5 (.system [[0,1,2,3,16,17,18,19,20,6,5],[4],[7],[9],[10],[15]]) (.forbid 3 6 6 (.system [[0],[2,3,16,17,18,19,20,21,6,5],[4],[7],[9],[10],[15]]) (.forbid 3 8 1 (.system [[0,1,2,3,16,8,7],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 3 8 2 (.system [[0],[2,3,16,17,8,7],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 3 8 3 (.system [[0],[2,3,16,17,18,8,7],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 3 8 4 (.system [[0],[2,3,16,17,18,19,8,7],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 3 8 5 (.system [[0,1,2,3,16,17,18,19,20,8,7],[4],[5],[9],[10],[15]]) (.forbid 3 8 6 (.system [[0],[2,3,16,17,18,19,20,21,8,7],[4],[5],[9],[10],[15]]) (certificate_2971_part_1))))))))))))))))))))

noncomputable def certificate_2971_part_3 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,16,5,6,7],[2,3,4],[9],[10,11,12,13,14,15]]) (.forbid 1 5 2 (.system [[0,1,16,17,5],[2,3,4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 5 3 (.system [[0,1,16,17,18,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 5 4 (.system [[0,1,16,17,18,19,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 5 5 (.system [[0,1,16,17,18,19,20,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 5 6 (.system [[0,1,16,17,18,19,20,21,5],[2,3,4],[7],[9],[10],[15]]) (.forbid 1 6 1 (.system [[0,1,16,6,5],[2,3,4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 6 2 (.system [[0,1,16,17,6,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 6 3 (.system [[0,1,16,17,18,6,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 6 4 (.system [[0,1,16,17,18,19,6,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 6 5 (.system [[0,1,16,17,18,19,20,6,5],[2,3,4],[7],[9],[10],[15]]) (.forbid 1 6 6 (.system [[0,1,16,17,18,19,20,21,6,5],[2],[4],[7],[9],[10],[15]]) (.forbid 1 8 1 (.system [[0,1,16,8,7],[2,3,4],[5],[9],[10,11,12,13,14,15]]) (.forbid 1 8 2 (.system [[0,1,16,17,8,7],[2],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 1 8 3 (.system [[0,1,16,17,18,8,7],[2],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 1 8 4 (.system [[0,1,16,17,18,19,8,7],[2],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 1 8 5 (.system [[0,1,16,17,18,19,20,8,7],[2,3,4],[5],[9],[10],[15]]) (.forbid 1 8 6 (.system [[0,1,16,17,18,19,20,21,8,7],[2],[4],[5],[9],[10],[15]]) (.forbid 2 3 1 (.system [[0,1,2,16,3,4],[5,6,7],[9],[10,11,12,13,14,15]]) (.forbid 2 6 1 (.system [[0,1,2,16,6,5],[4],[7,8,9],[10,11,12,13,14,15]]) (certificate_2971_part_2))))))))))))))))))))

noncomputable def certificate_2971_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[0,16,17,18,6,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 6 4 (.system [[0,16,17,18,19,6,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 6 5 (.system [[0,16,17,18,19,20,6,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 6 6 (.system [[2,1,0,16,17,18,19,20,21,6,5],[4],[7],[9],[10],[15]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,16,8,7],[5],[9],[10,11,12,13,14,15]]) (.forbid 0 8 2 (.system [[2,1,0,16,17,8,7],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 0 8 3 (.system [[0,16,17,18,8,7],[2],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 0 8 4 (.system [[0,16,17,18,19,8,7],[2],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 0 8 5 (.system [[0,16,17,18,19,20,8,7],[2],[4],[5],[9],[10,11,12,13,14,15]]) (.forbid 0 8 6 (.system [[2,1,0,16,17,18,19,20,21,8,7],[4],[5],[9],[10],[15]]) (.forbid 0 9 1 (.system [[4,3,2,1,0,16,9,8,7,6,5],[10,11,12,13,14,15]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,16,10,11,12,13,14,15],[5,6,7,8,9]]) (.forbid 1 2 1 (.system [[0,1,16,2,3,4],[5,6,7],[9],[10,11,12,13,14,15]]) (.forbid 1 3 1 (.system [[0,1,16,3,2],[4],[5,6,7],[9],[10,11,12,13,14,15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3,2],[4],[5,6,7],[9],[10],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,2],[4],[5],[7],[9],[10],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3,2],[5,6,7],[9],[10,11,12,13,14,15]]) (certificate_2971_part_3))))))))))))))))))))

noncomputable def certificate_2971 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4],[5,6,7],[9],[10,11,12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2,3,4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2,3,4],[5],[7],[9],[10],[15]]) (.forbid 0 3 1 (.system [[0,16,3,2],[4],[5,6,7,8,9],[10,11,12,13,14,15]]) (.forbid 0 3 2 (.system [[0,16,17,3,2],[4],[5,6,7],[9],[10,11,12,13,14,15]]) (.forbid 0 3 3 (.system [[0,16,17,18,3,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 3 4 (.system [[0,16,17,18,19,3,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 3 5 (.system [[0,16,17,18,19,20,3,2],[4],[5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3,2],[4],[5,6,7],[9],[10],[15]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,16,5,6,7,8,9],[10,11,12,13,14,15]]) (.forbid 0 5 2 (.system [[4,3,2,1,0,16,17,5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 5 3 (.system [[2,1,0,16,17,18,5],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 5 4 (.system [[0,16,17,18,19,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 5 5 (.system [[0,16,17,18,19,20,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 5 6 (.system [[0,16,17,18,19,20,21,5],[2],[4],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,16,6,5],[7],[9],[10,11,12,13,14,15]]) (.forbid 0 6 2 (.system [[2,1,0,16,17,6,5],[4],[7],[9],[10,11,12,13,14,15]]) (certificate_2971_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates094
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2991_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,16,17,18,6,5],[4],[7,8,9,10,11],[12],[15]]) (.forbid 0 6 4 (.system [[0,16,17,18,19,6,5],[2],[4],[7,8,9,10,11],[12],[15]]) (.forbid 0 6 5 (.system [[0,16,17,18,19,20,6,5],[2],[4],[7,8,9,10,11],[12],[15]]) (.forbid 0 6 6 (.system [[2,1,0,16,17,18,19,20,21,6,5],[4],[7],[11],[12],[15]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,16,8,9,10,11],[5],[7],[12,13,14,15]]) (.forbid 0 8 2 (.system [[2,1,0,16,17,8,9,10,11],[4],[5],[7],[12,13,14,15]]) (.forbid 0 8 3 (.system [[4,3,2,1,0,16,17,18,8,7],[5],[11],[12,13,14,15]]) (.forbid 0 8 4 (.system [[2,1,0,16,17,18,19,8,7],[4],[5],[11],[12,13,14,15]]) (.forbid 0 8 5 (.system [[0,16,17,18,19,20,8,7],[2],[4],[5],[11],[12,13,14,15]]) (.forbid 0 8 6 (.system [[2,1,0,16,17,18,19,20,21,8,7],[4],[5],[11],[12],[15]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,16,10,9,8,7],[5],[11],[12,13,14,15]]) (.forbid 0 11 1 (.system [[4,3,2,1,0,16,11,10,9,8,7,6,5],[12,13,14,15]]) (.forbid 1 2 1 (.system [[0,1,16,2,3,4],[5],[7,8,9,10,11],[12,13,14,15]]) (.forbid 1 3 1 (.system [[0,1,16,3,2],[4],[5],[7,8,9,10,11],[12,13,14,15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3,2],[4],[5,6,7,8,9,10,11],[12],[15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3,2],[4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3,2],[4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3,2],[4],[5,6,7],[11],[12],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,2],[4],[5],[7],[11],[12],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3,2],[5],[7,8,9,10,11],[12,13,14,15]]) (certificate_2991_part_3))))))))))))))))))))

noncomputable def certificate_2991 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4],[5],[7,8,9,10,11],[12,13,14,15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2],[4],[5],[7,8,9,10,11],[12,13,14,15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2,3,4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2],[4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2,3,4],[5],[7],[11],[12],[15]]) (.forbid 0 3 1 (.system [[0,16,3,2],[4],[5,6,7,8,9,10,11],[12,13,14,15]]) (.forbid 0 3 2 (.system [[0,16,17,3,2],[4],[5],[7,8,9,10,11],[12,13,14,15]]) (.forbid 0 3 3 (.system [[0,16,17,18,3,2],[4],[5,6,7,8,9,10,11],[12],[15]]) (.forbid 0 3 4 (.system [[0,16,17,18,19,3,2],[4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 0 3 5 (.system [[0,16,17,18,19,20,3,2],[4],[5],[7,8,9,10,11],[12],[15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3,2],[4],[5,6,7],[11],[12],[15]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,16,5,6,7,8,9,10,11],[12,13,14,15]]) (.forbid 0 5 2 (.system [[2,1,0,16,17,5],[4],[7,8,9,10,11],[12,13,14,15]]) (.forbid 0 5 3 (.system [[0,16,17,18,5],[2],[4],[7,8,9,10,11],[12,13,14,15]]) (.forbid 0 5 4 (.system [[2,1,0,16,17,18,19,5],[4],[7,8,9,10,11],[12],[15]]) (.forbid 0 5 5 (.system [[0,16,17,18,19,20,5],[2],[4],[7,8,9,10,11],[12],[15]]) (.forbid 0 5 6 (.system [[0,16,17,18,19,20,21,5],[2],[4],[7,8,9,10,11],[12],[15]]) (.forbid 0 6 1 (.system [[2,1,0,16,6,5],[4],[7,8,9,10,11],[12,13,14,15]]) (.forbid 0 6 2 (.system [[0,16,17,6,5],[2],[4],[7,8,9,10,11],[12,13,14,15]]) (certificate_2991_part_4))))))))))))))))))))

noncomputable def certificate_2992_part_1 : FiniteCertificate := .forbid 3 8 4 (.system [[0],[2,3,17,18,19,20,8,7],[4],[5],[11],[12,13,14,15,16]]) (.forbid 3 8 5 (.system [[0],[2,3,17,18,19,20,21,8,7],[4],[5],[11],[12,13,14,15,16]]) (.forbid 3 8 6 (.system [[0,1,2,3,17,18,19,20,21,22,8,7],[4],[5],[11],[12],[16]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,17,5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 4 6 1 (.system [[0,1,2],[4,17,6,5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 4 8 1 (.system [[0,1,2,3,4,17,8,9,10,11],[5],[7],[12,13,14,15,16]]) (.forbid 5 6 1 (.system [[0,1,2],[4],[5,17,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 5 6 2 (.system [[0],[2],[4],[5,17,18,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,17,18,19,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 5 6 4 (.system [[0,1,2],[4],[5,17,18,19,20,6,7,8,9,10,11],[12],[16]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,17,18,19,20,21,6,7,8,9,10,11],[12],[16]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,17,18,19,20,21,22,6,7,8,9,10,11],[12],[16]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[5,17,8,9,10,11],[7],[12,13,14,15,16]]) (.forbid 5 8 2 (.system [[0,1,2],[4],[5,17,18,8,9,10,11],[7],[12,13,14,15,16]]) (.forbid 5 8 3 (.system [[0,1,2,3,4],[5,17,18,19,8,7],[11],[12,13,14,15,16]]) (.forbid 5 8 4 (.system [[0,1,2],[4],[5,17,18,19,20,8,7],[11],[12,13,14,15,16]]) (.forbid 5 8 5 (.system [[0],[2],[4],[5,17,18,19,20,21,8,7],[11],[12,13,14,15,16]]) (.forbid 5 8 6 (.system [[0],[2],[4],[5,17,18,19,20,21,22,8,7],[11],[12,13,14,15,16]]) (.forbid 5 10 1 (.system [[0,1,2,3,4],[5,17,10,9,8,7],[11],[12,13,14,15,16]]) (.forbid 5 12 1 (.system [[0,1,2,3,4],[11,10,9,8,7,6,5,17,12,13,14,15,16]]) (certificate_2992_part_0))))))))))))))))))))

noncomputable def certificate_2992_part_2 : FiniteCertificate := .forbid 2 3 1 (.system [[0,1,2,17,3,4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 2 6 1 (.system [[0,1,2,17,6,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 2 8 1 (.system [[0,1,2,17,8,9,10,11],[4],[5,6,7],[12,13,14,15,16]]) (.forbid 3 4 1 (.system [[0,1,2,3,17,4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 3 5 1 (.system [[0,1,2,3,17,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 3 5 2 (.system [[0],[2,3,17,18,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 3 5 3 (.system [[0],[2,3,17,18,19,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 3 5 4 (.system [[0,1,2,3,17,18,19,20,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 3 5 5 (.system [[0],[2,3,17,18,19,20,21,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 3 5 6 (.system [[0],[2,3,17,18,19,20,21,22,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 3 6 1 (.system [[0],[2,3,17,6,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 3 6 2 (.system [[0],[2,3,17,18,6,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 3 6 3 (.system [[0,1,2,3,17,18,19,6,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 3 6 4 (.system [[0],[2,3,17,18,19,20,6,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 3 6 5 (.system [[0],[2,3,17,18,19,20,21,6,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 3 6 6 (.system [[0,1,2,3,17,18,19,20,21,22,6,5],[4],[7],[11],[12],[16]]) (.forbid 3 7 1 (.system [[0,1,2,3,17,7,8,9,10,11],[4],[5],[12,13,14,15,16]]) (.forbid 3 8 1 (.system [[0,1,2,3,17,8,9,10,11],[4],[5],[7],[12,13,14,15,16]]) (.forbid 3 8 2 (.system [[0,1,2,3,17,18,8,7,6,5],[4],[11],[12,13,14,15,16]]) (.forbid 3 8 3 (.system [[0,1,2,3,17,18,19,8,7],[4],[5],[11],[12,13,14,15,16]]) (certificate_2992_part_1))))))))))))))))))))

noncomputable def certificate_2992_part_3 : FiniteCertificate := .forbid 1 4 1 (.system [[0,1,17,4,3,2],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 5 1 (.system [[0,1,17,5],[2,3,4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 5 2 (.system [[0,1,17,18,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 5 3 (.system [[0,1,17,18,19,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 5 4 (.system [[0,1,17,18,19,20,5],[2,3,4],[7,8,9,10,11],[12],[16]]) (.forbid 1 5 5 (.system [[0,1,17,18,19,20,21,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 1 5 6 (.system [[0,1,17,18,19,20,21,22,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 1 6 1 (.system [[0,1,17,6,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 6 2 (.system [[0,1,17,18,6,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 6 3 (.system [[0,1,17,18,19,6,5],[2,3,4],[7,8,9,10,11],[12],[16]]) (.forbid 1 6 4 (.system [[0,1,17,18,19,20,6,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 1 6 5 (.system [[0,1,17,18,19,20,21,6,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 1 6 6 (.system [[0,1,17,18,19,20,21,22,6,5],[2,3,4],[7],[11],[12],[16]]) (.forbid 1 7 1 (.system [[0,1,17,7,8,9,10,11],[2,3,4],[5],[12,13,14,15,16]]) (.forbid 1 8 1 (.system [[0,1,17,8,9,10,11],[2,3,4],[5],[7],[12,13,14,15,16]]) (.forbid 1 8 2 (.system [[0,1,17,18,8,7,6,5],[2,3,4],[11],[12,13,14,15,16]]) (.forbid 1 8 3 (.system [[0,1,17,18,19,8,7],[2,3,4],[5],[11],[12,13,14,15,16]]) (.forbid 1 8 4 (.system [[0,1,17,18,19,20,8,7],[2],[4],[5],[11],[12,13,14,15,16]]) (.forbid 1 8 5 (.system [[0,1,17,18,19,20,21,8,7],[2],[4],[5],[11],[12,13,14,15,16]]) (.forbid 1 8 6 (.system [[0,1,17,18,19,20,21,22,8,7],[2,3,4],[5],[11],[12],[16]]) (certificate_2992_part_2))))))))))))))))))))

noncomputable def certificate_2992_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[0,17,18,19,6,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 6 4 (.system [[2,1,0,17,18,19,20,6,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 0 6 5 (.system [[0,17,18,19,20,21,6,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 0 6 6 (.system [[0,17,18,19,20,21,22,6,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,17,8,9,10,11],[5],[7],[12,13,14,15,16]]) (.forbid 0 8 2 (.system [[2,1,0,17,18,8,9,10,11],[4],[5],[7],[12,13,14,15,16]]) (.forbid 0 8 3 (.system [[4,3,2,1,0,17,18,19,8,7],[5],[11],[12,13,14,15,16]]) (.forbid 0 8 4 (.system [[2,1,0,17,18,19,20,8,7],[4],[5],[11],[12,13,14,15,16]]) (.forbid 0 8 5 (.system [[0,17,18,19,20,21,8,7],[2],[4],[5],[11],[12,13,14,15,16]]) (.forbid 0 8 6 (.system [[0,17,18,19,20,21,22,8,7],[2],[4],[5],[11],[12,13,14,15,16]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,17,10,9,8,7],[5],[11],[12,13,14,15,16]]) (.forbid 0 11 1 (.system [[4,3,2,1,0,17,11,10,9,8,7,6,5],[12,13,14,15,16]]) (.forbid 0 12 1 (.system [[4,3,2,1,0,17,12,13,14,15,16],[5,6,7,8,9,10,11]]) (.forbid 1 2 1 (.system [[0,1,17,2,3,4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 3 1 (.system [[0,1,17,3,2],[4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 3 2 (.system [[0,1,17,18,3,2],[4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 3 3 (.system [[0,1,17,18,19,3,2],[4],[5,6,7,8,9,10,11],[12],[16]]) (.forbid 1 3 4 (.system [[0,1,17,18,19,20,3,2],[4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 1 3 5 (.system [[0,1,17,18,19,20,21,3,2],[4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 1 3 6 (.system [[0,1,17,18,19,20,21,22,3,2],[4],[5,6,7],[11],[12],[16]]) (certificate_2992_part_3))))))))))))))))))))

noncomputable def certificate_2992 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2,3,4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 1 2 (.system [[0,17,18,1,2],[4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1,2],[4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1,2,3,4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2],[4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1,2],[4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 0 3 1 (.system [[0,17,3,2],[4],[5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 3 2 (.system [[0,17,18,3,2],[4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 3 3 (.system [[0,17,18,19,3,2],[4],[5],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 3 4 (.system [[0,17,18,19,20,3,2],[4],[5,6,7,8,9,10,11],[12],[16]]) (.forbid 0 3 5 (.system [[0,17,18,19,20,21,3,2],[4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 0 3 6 (.system [[0,17,18,19,20,21,22,3,2],[4],[5],[7,8,9,10,11],[12],[16]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,17,5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 5 2 (.system [[2,1,0,17,18,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 5 3 (.system [[0,17,18,19,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 5 4 (.system [[0,17,18,19,20,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 5 5 (.system [[2,1,0,17,18,19,20,21,5],[4],[7,8,9,10,11],[12],[16]]) (.forbid 0 5 6 (.system [[0,17,18,19,20,21,22,5],[2],[4],[7,8,9,10,11],[12],[16]]) (.forbid 0 6 1 (.system [[2,1,0,17,6,5],[4],[7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 6 2 (.system [[0,17,18,6,5],[2],[4],[7,8,9,10,11],[12,13,14,15,16]]) (certificate_2992_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates095
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_3018_part_1 : FiniteCertificate := .forbid 3 5 2 (.system [[0,1,2,3,15,16,5,4],[6],[8],[9],[11,12,13,14]]) (.forbid 3 5 3 (.system [[0],[2,3,15,16,17,5,4],[6],[8],[9],[11,12,13,14]]) (.forbid 3 5 4 (.system [[0,1,2,3,15,16,17,18,5,4],[6],[8],[9],[11],[14]]) (.forbid 3 5 5 (.system [[0],[2,3,15,16,17,18,19,5,4],[6],[8],[9],[11],[14]]) (.forbid 3 5 6 (.system [[0],[2,3,15,16,17,18,19,20,5,4],[6],[8],[9],[11],[14]]) (.forbid 3 7 1 (.system [[0,1,2,3,15,7,6,5,4],[8],[9],[11,12,13,14]]) (.forbid 3 7 2 (.system [[0,1,2,3,15,16,7,6],[4],[8],[9],[11,12,13,14]]) (.forbid 3 7 3 (.system [[0],[2,3,15,16,17,7,6],[4],[8],[9],[11,12,13,14]]) (.forbid 3 7 4 (.system [[0,1,2,3,15,16,17,18,7,6],[4],[8],[9],[11],[14]]) (.forbid 3 7 5 (.system [[0],[2,3,15,16,17,18,19,7,6],[4],[8],[9],[11],[14]]) (.forbid 3 7 6 (.system [[0],[2,3,15,16,17,18,19,20,7,6],[4],[8],[9],[11],[14]]) (.forbid 3 9 1 (.system [[0,1,2,3,15,9],[4,5,6,7,8],[11,12,13,14]]) (.forbid 3 9 2 (.system [[0,1,2,3,15,16,9],[4,5,6],[8],[11,12,13,14]]) (.forbid 3 9 3 (.system [[0,1,2,3,15,16,17,9],[4],[6],[8],[11,12,13,14]]) (.forbid 3 9 4 (.system [[0],[2,3,15,16,17,18,9],[4],[6],[8],[11,12,13,14]]) (.forbid 3 9 5 (.system [[0,1,2,3,15,16,17,18,19,9],[4],[6],[8],[11],[14]]) (.forbid 3 9 6 (.system [[0],[2,3,15,16,17,18,19,20,9],[4],[6],[8],[11],[14]]) (.forbid 5 7 1 (.system [[0,1,2,3,4,5,15,7,6],[8],[9],[11,12,13,14]]) (.forbid 5 7 2 (.system [[0,1,2],[4,5,15,16,7,6],[8],[9],[11,12,13,14]]) (.forbid 5 7 3 (.system [[0],[2],[4,5,15,16,17,7,6],[8],[9],[11,12,13,14]]) (certificate_3018_part_0))))))))))))))))))))

noncomputable def certificate_3018_part_2 : FiniteCertificate := .forbid 1 5 3 (.system [[0,1,15,16,17,5,4],[2],[6],[8],[9],[11,12,13,14]]) (.forbid 1 5 4 (.system [[0,1,15,16,17,18,5,4,3,2],[6],[8],[9],[11],[14]]) (.forbid 1 5 5 (.system [[0,1,15,16,17,18,19,5,4],[2],[6],[8],[9],[11],[14]]) (.forbid 1 5 6 (.system [[0,1,15,16,17,18,19,20,5,4],[2],[6],[8],[9],[11],[14]]) (.forbid 1 7 1 (.system [[0,1,15,7,6,5,4,3,2],[8],[9],[11,12,13,14]]) (.forbid 1 7 2 (.system [[0,1,15,16,7,6],[2,3,4],[8],[9],[11,12,13,14]]) (.forbid 1 7 3 (.system [[0,1,15,16,17,7,6],[2],[4],[8],[9],[11,12,13,14]]) (.forbid 1 7 4 (.system [[0,1,15,16,17,18,7,6],[2,3,4],[8],[9],[11],[14]]) (.forbid 1 7 5 (.system [[0,1,15,16,17,18,19,7,6],[2],[4],[8],[9],[11],[14]]) (.forbid 1 7 6 (.system [[0,1,15,16,17,18,19,20,7,6],[2],[4],[8],[9],[11],[14]]) (.forbid 1 9 1 (.system [[0,1,15,9],[2,3,4,5,6,7,8],[11,12,13,14]]) (.forbid 1 9 2 (.system [[0,1,15,16,9],[2,3,4,5,6],[8],[11,12,13,14]]) (.forbid 1 9 3 (.system [[0,1,15,16,17,9],[2,3,4],[6],[8],[11,12,13,14]]) (.forbid 1 9 4 (.system [[0,1,15,16,17,18,9],[2],[4],[6],[8],[11,12,13,14]]) (.forbid 1 9 5 (.system [[0,1,15,16,17,18,19,9],[2,3,4],[6],[8],[11],[14]]) (.forbid 1 9 6 (.system [[0,1,15,16,17,18,19,20,9],[2],[4],[6],[8],[11],[14]]) (.forbid 2 3 1 (.system [[0,1,2,15,3,4,5,6,7,8],[9],[11,12,13,14]]) (.forbid 2 5 1 (.system [[0,1,2,15,5,4],[6,7,8],[9,10,11,12,13,14]]) (.forbid 2 7 1 (.system [[0,1,2,15,7,6,5,4],[8],[9,10,11,12,13,14]]) (.forbid 3 5 1 (.system [[0,1,2,3,15,5,4],[6,7,8],[9],[11,12,13,14]]) (certificate_3018_part_1))))))))))))))))))))

noncomputable def certificate_3018_part_3 : FiniteCertificate := .forbid 0 7 3 (.system [[2,1,0,15,16,17,7,6],[4],[8],[9],[11,12,13,14]]) (.forbid 0 7 4 (.system [[0,15,16,17,18,7,6],[2],[4],[8],[9],[11,12,13,14]]) (.forbid 0 7 5 (.system [[2,1,0,15,16,17,18,19,7,6],[4],[8],[9],[11],[14]]) (.forbid 0 7 6 (.system [[0,15,16,17,18,19,20,7,6],[2],[4],[8],[9],[11],[14]]) (.forbid 0 9 1 (.system [[8,7,6,5,4,3,2,1,0,15,9,10,11,12,13,14]]) (.forbid 0 9 2 (.system [[6,5,4,3,2,1,0,15,16,9],[8],[11,12,13,14]]) (.forbid 0 9 3 (.system [[4,3,2,1,0,15,16,17,9],[6],[8],[11,12,13,14]]) (.forbid 0 9 4 (.system [[2,1,0,15,16,17,18,9],[4],[6],[8],[11,12,13,14]]) (.forbid 0 9 5 (.system [[0,15,16,17,18,19,9],[2],[4],[6],[8],[11,12,13,14]]) (.forbid 0 9 6 (.system [[2,1,0,15,16,17,18,19,20,9],[4],[6],[8],[11],[14]]) (.forbid 0 10 1 (.system [[6,5,4,3,2,1,0,15,10,9],[8],[11,12,13,14]]) (.forbid 1 2 1 (.system [[0,1,15,2,3,4,5,6,7,8],[9],[11,12,13,14]]) (.forbid 1 3 1 (.system [[0,1,15,3,2],[4,5,6,7,8],[9],[11,12,13,14]]) (.forbid 1 3 2 (.system [[0,1,15,16,3,2],[4,5,6],[8],[9],[11,12,13,14]]) (.forbid 1 3 3 (.system [[0,1,15,16,17,3,2],[4],[6],[8],[9],[11,12,13,14]]) (.forbid 1 3 4 (.system [[0,1,15,16,17,18,3,2],[4,5,6],[8],[9],[11],[14]]) (.forbid 1 3 5 (.system [[0,1,15,16,17,18,19,3,2],[4],[6],[8],[9],[11],[14]]) (.forbid 1 3 6 (.system [[0,1,15,16,17,18,19,20,3,2],[4],[6],[8],[9],[11],[14]]) (.forbid 1 5 1 (.system [[0,1,15,5,4,3,2],[6,7,8],[9],[11,12,13,14]]) (.forbid 1 5 2 (.system [[0,1,15,16,5,4,3,2],[6],[8],[9],[11,12,13,14]]) (certificate_3018_part_2))))))))))))))))))))

noncomputable def certificate_3018 : FiniteCertificate := .forbid 0 1 1 (.system [[0,15,1,2,3,4,5,6,7,8],[9],[11,12,13,14]]) (.forbid 0 1 2 (.system [[0,15,16,1,2,3,4,5,6],[8],[9],[11,12,13,14]]) (.forbid 0 1 3 (.system [[0,15,16,17,1,2,3,4],[6],[8],[9],[11,12,13,14]]) (.forbid 0 1 4 (.system [[0,15,16,17,18,1,2],[4],[6],[8],[9],[11,12,13,14]]) (.forbid 0 1 5 (.system [[0,15,16,17,18,19,1,2,3,4],[6],[8],[9],[11],[14]]) (.forbid 0 1 6 (.system [[0,15,16,17,18,19,20,1,2],[4],[6],[8],[9],[11],[14]]) (.forbid 0 3 1 (.system [[0,15,3,2],[4,5,6,7,8],[9,10,11,12,13,14]]) (.forbid 0 3 2 (.system [[0,15,16,3,2],[4,5,6,7,8],[9],[11,12,13,14]]) (.forbid 0 3 3 (.system [[0,15,16,17,3,2],[4,5,6],[8],[9],[11,12,13,14]]) (.forbid 0 3 4 (.system [[0,15,16,17,18,3,2],[4],[6],[8],[9],[11,12,13,14]]) (.forbid 0 3 5 (.system [[0,15,16,17,18,19,3,2],[4,5,6],[8],[9],[11],[14]]) (.forbid 0 3 6 (.system [[0,15,16,17,18,19,20,3,2],[4],[6],[8],[9],[11],[14]]) (.forbid 0 5 1 (.system [[2,1,0,15,5,4],[6,7,8],[9,10,11,12,13,14]]) (.forbid 0 5 2 (.system [[2,1,0,15,16,5,4],[6,7,8],[9],[11,12,13,14]]) (.forbid 0 5 3 (.system [[2,1,0,15,16,17,5,4],[6],[8],[9],[11,12,13,14]]) (.forbid 0 5 4 (.system [[0,15,16,17,18,5,4],[2],[6],[8],[9],[11,12,13,14]]) (.forbid 0 5 5 (.system [[2,1,0,15,16,17,18,19,5,4],[6],[8],[9],[11],[14]]) (.forbid 0 5 6 (.system [[0,15,16,17,18,19,20,5,4],[2],[6],[8],[9],[11],[14]]) (.forbid 0 7 1 (.system [[4,3,2,1,0,15,7,6],[8],[9,10,11,12,13,14]]) (.forbid 0 7 2 (.system [[4,3,2,1,0,15,16,7,6],[8],[9],[11,12,13,14]]) (certificate_3018_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates096
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_3044_part_1 : FiniteCertificate := .forbid 3 8 6 (.system [[0],[2,3,16,17,18,19,20,21,8,7,6],[4],[9],[11],[13],[15]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,16,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 4 7 1 (.system [[0,1,2,3,4,16,7,8,9,10,11,12,13,14,15],[6]]) (.forbid 4 8 1 (.system [[0,1,2,3,4,16,8,7,6],[9,10,11,12,13,14,15]]) (.forbid 5 7 1 (.system [[0,1,2,3,4,5,16,7,6],[9,10,11,12,13,14,15]]) (.forbid 5 7 2 (.system [[0,1,2,3,4,5,16,17,7,6],[9,10,11,12,13],[15]]) (.forbid 5 7 3 (.system [[0,1,2,3,4,5,16,17,18,7,6],[9,10,11],[13],[15]]) (.forbid 5 7 4 (.system [[0,1,2,3,4,5,16,17,18,19,7,6],[9],[11],[13],[15]]) (.forbid 5 7 5 (.system [[0,1,2],[4,5,16,17,18,19,20,7,6],[9],[11],[13],[15]]) (.forbid 5 7 6 (.system [[0],[2],[4,5,16,17,18,19,20,21,7,6],[9],[11],[13],[15]]) (.forbid 5 8 1 (.system [[0,1,2,3,4,5,16,8,7,6],[9,10,11,12,13],[15]]) (.forbid 5 8 2 (.system [[0,1,2,3,4,5,16,17,8,7,6],[9,10,11],[13],[15]]) (.forbid 5 8 3 (.system [[0,1,2,3,4,5,16,17,18,8,7,6],[9],[11],[13],[15]]) (.forbid 5 8 4 (.system [[0,1,2],[4,5,16,17,18,19,8,7,6],[9],[11],[13],[15]]) (.forbid 5 8 5 (.system [[0],[2],[4,5,16,17,18,19,20,8,7,6],[9],[11],[13],[15]]) (.forbid 5 8 6 (.system [[0],[2],[4,5,16,17,18,19,20,21,8,7,6],[9],[11],[13],[15]]) (.forbid 7 8 1 (.system [[0,1,2,3,4,5,6,7,16,8,9,10,11,12,13],[15]]) (.forbid 7 8 2 (.system [[0,1,2,3,4,5,6,7,16,17,8,9,10,11],[13],[15]]) (.forbid 7 8 3 (.system [[0,1,2,3,4,5,6,7,16,17,18,8,9],[11],[13],[15]]) (.forbid 7 8 4 (.system [[0,1,2,3,4],[6,7,16,17,18,19,8,9],[11],[13],[15]]) (certificate_3044_part_0))))))))))))))))))))

noncomputable def certificate_3044_part_2 : FiniteCertificate := .forbid 2 7 1 (.system [[0,1,2,16,7,8,9,10,11,12,13,14,15],[4,5,6]]) (.forbid 2 8 1 (.system [[0,1,2,16,8,7,6,5,4],[9,10,11,12,13,14,15]]) (.forbid 3 4 1 (.system [[0,1,2,3,16,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 3 5 1 (.system [[0,1,2,3,16,5,4],[6,7,8,9,10,11,12,13],[15]]) (.forbid 3 5 2 (.system [[0,1,2,3,16,17,5,4],[6,7,8,9,10,11],[13],[15]]) (.forbid 3 5 3 (.system [[0,1,2,3,16,17,18,5,4],[6,7,8,9],[11],[13],[15]]) (.forbid 3 5 4 (.system [[0],[2,3,16,17,18,19,5,4],[6,7,8,9],[11],[13],[15]]) (.forbid 3 5 5 (.system [[0,1,2,3,16,17,18,19,20,5,4],[6],[9],[11],[13],[15]]) (.forbid 3 5 6 (.system [[0],[2,3,16,17,18,19,20,21,5,4],[6],[9],[11],[13],[15]]) (.forbid 3 7 1 (.system [[0,1,2,3,16,7,6,5,4],[9,10,11,12,13,14,15]]) (.forbid 3 7 2 (.system [[0,1,2,3,16,17,7,6,5,4],[9,10,11,12,13],[15]]) (.forbid 3 7 3 (.system [[0,1,2,3,16,17,18,7,6,5,4],[9,10,11],[13],[15]]) (.forbid 3 7 4 (.system [[0,1,2,3,16,17,18,19,7,6,5,4],[9],[11],[13],[15]]) (.forbid 3 7 5 (.system [[0,1,2,3,16,17,18,19,20,7,6],[4],[9],[11],[13],[15]]) (.forbid 3 7 6 (.system [[0],[2,3,16,17,18,19,20,21,7,6],[4],[9],[11],[13],[15]]) (.forbid 3 8 1 (.system [[0,1,2,3,16,8,7,6,5,4],[9,10,11,12,13],[15]]) (.forbid 3 8 2 (.system [[0,1,2,3,16,17,8,7,6,5,4],[9,10,11],[13],[15]]) (.forbid 3 8 3 (.system [[0,1,2,3,16,17,18,8,7,6,5,4],[9],[11],[13],[15]]) (.forbid 3 8 4 (.system [[0,1,2,3,16,17,18,19,8,7,6],[4],[9],[11],[13],[15]]) (.forbid 3 8 5 (.system [[0],[2,3,16,17,18,19,20,8,7,6],[4],[9],[11],[13],[15]]) (certificate_3044_part_1))))))))))))))))))))

noncomputable def certificate_3044_part_3 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,16,5,4,3,2],[6,7,8,9,10,11,12,13],[15]]) (.forbid 1 5 2 (.system [[0,1,16,17,5,4,3,2],[6,7,8,9,10,11],[13],[15]]) (.forbid 1 5 3 (.system [[0,1,16,17,18,5,4,3,2],[6,7,8,9],[11],[13],[15]]) (.forbid 1 5 4 (.system [[0,1,16,17,18,19,5,4],[2],[6,7,8,9],[11],[13],[15]]) (.forbid 1 5 5 (.system [[0,1,16,17,18,19,20,5,4,3,2],[6],[9],[11],[13],[15]]) (.forbid 1 5 6 (.system [[0,1,16,17,18,19,20,21,5,4],[2],[6],[9],[11],[13],[15]]) (.forbid 1 7 1 (.system [[0,1,16,7,6,5,4,3,2],[9,10,11,12,13,14,15]]) (.forbid 1 7 2 (.system [[0,1,16,17,7,6,5,4,3,2],[9,10,11,12,13],[15]]) (.forbid 1 7 3 (.system [[0,1,16,17,18,7,6,5,4,3,2],[9,10,11],[13],[15]]) (.forbid 1 7 4 (.system [[0,1,16,17,18,19,7,6,5,4,3,2],[9],[11],[13],[15]]) (.forbid 1 7 5 (.system [[0,1,16,17,18,19,20,7,6],[2,3,4],[9],[11],[13],[15]]) (.forbid 1 7 6 (.system [[0,1,16,17,18,19,20,21,7,6],[2],[4],[9],[11],[13],[15]]) (.forbid 1 8 1 (.system [[0,1,16,8,7,6,5,4,3,2],[9,10,11,12,13],[15]]) (.forbid 1 8 2 (.system [[0,1,16,17,8,7,6,5,4,3,2],[9,10,11],[13],[15]]) (.forbid 1 8 3 (.system [[0,1,16,17,18,8,7,6,5,4,3,2],[9],[11],[13],[15]]) (.forbid 1 8 4 (.system [[0,1,16,17,18,19,8,7,6],[2,3,4],[9],[11],[13],[15]]) (.forbid 1 8 5 (.system [[0,1,16,17,18,19,20,8,7,6],[2],[4],[9],[11],[13],[15]]) (.forbid 1 8 6 (.system [[0,1,16,17,18,19,20,21,8,7,6],[2],[4],[9],[11],[13],[15]]) (.forbid 2 3 1 (.system [[0,1,2,16,3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 2 5 1 (.system [[0,1,2,16,5,4],[6,7,8,9,10,11,12,13,14,15]]) (certificate_3044_part_2))))))))))))))))))))

noncomputable def certificate_3044_part_4 : FiniteCertificate := .forbid 0 7 3 (.system [[4,3,2,1,0,16,17,18,7,6],[9,10,11,12,13],[15]]) (.forbid 0 7 4 (.system [[4,3,2,1,0,16,17,18,19,7,6],[9,10,11],[13],[15]]) (.forbid 0 7 5 (.system [[4,3,2,1,0,16,17,18,19,20,7,6],[9],[11],[13],[15]]) (.forbid 0 7 6 (.system [[2,1,0,16,17,18,19,20,21,7,6],[4],[9],[11],[13],[15]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,16,8,7,6],[9,10,11,12,13,14,15]]) (.forbid 0 8 2 (.system [[4,3,2,1,0,16,17,8,7,6],[9,10,11,12,13],[15]]) (.forbid 0 8 3 (.system [[4,3,2,1,0,16,17,18,8,7,6],[9,10,11],[13],[15]]) (.forbid 0 8 4 (.system [[4,3,2,1,0,16,17,18,19,8,7,6],[9],[11],[13],[15]]) (.forbid 0 8 5 (.system [[2,1,0,16,17,18,19,20,8,7,6],[4],[9],[11],[13],[15]]) (.forbid 0 8 6 (.system [[0,16,17,18,19,20,21,8,7,6],[2],[4],[9],[11],[13],[15]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,16,10,9,8,7,6],[11,12,13,14,15]]) (.forbid 0 12 1 (.system [[9,8,7,6,5,4,3,2,1,0,16,12,11],[13,14,15]]) (.forbid 1 2 1 (.system [[0,1,16,2,3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 1 3 1 (.system [[0,1,16,3,2],[4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 1 3 2 (.system [[0,1,16,17,3,2],[4,5,6,7,8,9,10,11],[13],[15]]) (.forbid 1 3 3 (.system [[0,1,16,17,18,3,2],[4,5,6,7,8,9],[11],[13],[15]]) (.forbid 1 3 4 (.system [[0,1,16,17,18,19,3,2],[4],[6,7,8,9],[11],[13],[15]]) (.forbid 1 3 5 (.system [[0,1,16,17,18,19,20,3,2],[4,5,6],[9],[11],[13],[15]]) (.forbid 1 3 6 (.system [[0,1,16,17,18,19,20,21,3,2],[4],[6],[9],[11],[13],[15]]) (.forbid 1 4 1 (.system [[0,1,16,4,3,2],[6,7,8,9,10,11,12,13,14,15]]) (certificate_3044_part_3))))))))))))))))))))

noncomputable def certificate_3044 : FiniteCertificate := .forbid 0 1 1 (.system [[0,16,1,2,3,4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 0 1 2 (.system [[0,16,17,1,2,3,4,5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 1 3 (.system [[0,16,17,18,1,2,3,4,5,6,7,8,9],[11],[13],[15]]) (.forbid 0 1 4 (.system [[0,16,17,18,19,1,2,3,4],[6,7,8,9],[11],[13],[15]]) (.forbid 0 1 5 (.system [[0,16,17,18,19,20,1,2],[4],[6,7,8,9],[11],[13],[15]]) (.forbid 0 1 6 (.system [[0,16,17,18,19,20,21,1,2,3,4],[6],[9],[11],[13],[15]]) (.forbid 0 3 1 (.system [[0,16,3,2],[4,5,6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 3 2 (.system [[0,16,17,3,2],[4,5,6,7,8,9,10,11,12,13],[15]]) (.forbid 0 3 3 (.system [[0,16,17,18,3,2],[4,5,6,7,8,9,10,11],[13],[15]]) (.forbid 0 3 4 (.system [[0,16,17,18,19,3,2],[4,5,6,7,8,9],[11],[13],[15]]) (.forbid 0 3 5 (.system [[0,16,17,18,19,20,3,2],[4],[6,7,8,9],[11],[13],[15]]) (.forbid 0 3 6 (.system [[0,16,17,18,19,20,21,3,2],[4,5,6],[9],[11],[13],[15]]) (.forbid 0 5 1 (.system [[2,1,0,16,5,4],[6,7,8,9,10,11,12,13,14,15]]) (.forbid 0 5 2 (.system [[2,1,0,16,17,5,4],[6,7,8,9,10,11,12,13],[15]]) (.forbid 0 5 3 (.system [[2,1,0,16,17,18,5,4],[6,7,8,9,10,11],[13],[15]]) (.forbid 0 5 4 (.system [[2,1,0,16,17,18,19,5,4],[6,7,8,9],[11],[13],[15]]) (.forbid 0 5 5 (.system [[0,16,17,18,19,20,5,4],[2],[6,7,8,9],[11],[13],[15]]) (.forbid 0 5 6 (.system [[2,1,0,16,17,18,19,20,21,5,4],[6],[9],[11],[13],[15]]) (.forbid 0 7 1 (.system [[6,5,4,3,2,1,0,16,7,8,9,10,11,12,13],[15]]) (.forbid 0 7 2 (.system [[4,3,2,1,0,16,17,7,6],[9,10,11,12,13,14,15]]) (certificate_3044_part_4))))))))))))))))))))

noncomputable def certificate_3067_part_1 : FiniteCertificate := .forbid 3 8 3 (.system [[0],[2,3,17,18,19,8,7,6,5,4],[9,10,11,12],[13],[16]]) (.forbid 3 8 4 (.system [[0,1,2,3,17,18,19,20,8,7,6,5,4],[9],[12],[13],[16]]) (.forbid 3 8 5 (.system [[0],[2,3,17,18,19,20,21,8,7,6,5,4],[9],[12],[13],[16]]) (.forbid 3 8 6 (.system [[0,1,2,3,17,18,19,20,21,22,8,7],[4],[9],[12],[13],[16]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,17,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 4 8 1 (.system [[0,1,2],[7,6,5,4,17,8,9,10,11,12],[13,14,15,16]]) (.forbid 5 6 1 (.system [[0,1,2,3,4,5,17,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 5 6 2 (.system [[0,1,2],[4,5,17,18,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 5 6 3 (.system [[0],[2],[4,5,17,18,19,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 5 6 4 (.system [[0,1,2],[4,5,17,18,19,20,6,7],[9,10,11,12],[13],[16]]) (.forbid 5 6 5 (.system [[0],[2],[4,5,17,18,19,20,21,6,7],[9,10,11,12],[13],[16]]) (.forbid 5 6 6 (.system [[0,1,2],[4,5,17,18,19,20,21,22,6,7],[9],[12],[13],[16]]) (.forbid 5 8 1 (.system [[0,1,2,3,4,5,17,8,7],[9,10,11,12],[13,14,15,16]]) (.forbid 5 8 2 (.system [[0,1,2],[4,5,17,18,8,7],[9,10,11,12],[13,14,15,16]]) (.forbid 5 8 3 (.system [[0],[2],[4,5,17,18,19,8,7],[9,10,11,12],[13,14,15,16]]) (.forbid 5 8 4 (.system [[0,1,2],[4,5,17,18,19,20,8,7],[9,10,11,12],[13],[16]]) (.forbid 5 8 5 (.system [[0],[2],[4,5,17,18,19,20,21,8,7],[9,10,11,12],[13],[16]]) (.forbid 5 8 6 (.system [[0,1,2],[4,5,17,18,19,20,21,22,8,7],[9],[12],[13],[16]]) (.forbid 5 9 1 (.system [[0,1,2,3,4],[7,6,5,17,9,10,11,12],[13,14,15,16]]) (.forbid 6 7 1 (.system [[0,1,2,3,4,5,6,17,7],[9,10,11,12],[13,14,15,16]]) (certificate_3067_part_0))))))))))))))))))))

noncomputable def certificate_3067_part_2 : FiniteCertificate := .forbid 2 3 1 (.system [[0,1,2,17,3,4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 2 5 1 (.system [[0,1,2,17,5,6,7,8,9,10,11,12],[4],[13,14,15,16]]) (.forbid 2 6 1 (.system [[0,1,2,17,6,5,4],[7,8,9,10,11,12],[13,14,15,16]]) (.forbid 2 8 1 (.system [[0,1,2,17,8,7,6,5,4],[9,10,11,12],[13,14,15,16]]) (.forbid 3 4 1 (.system [[0,1,2,3,17,4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 3 5 1 (.system [[0,1,2,3,17,5,4],[7,8,9,10,11,12],[13,14,15,16]]) (.forbid 3 5 2 (.system [[0,1,2,3,17,18,5,4],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 3 5 3 (.system [[0],[2,3,17,18,19,5,4],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 3 5 4 (.system [[0,1,2,3,17,18,19,20,5,4],[7],[9,10,11,12],[13],[16]]) (.forbid 3 5 5 (.system [[0],[2,3,17,18,19,20,21,5,4],[7],[9,10,11,12],[13],[16]]) (.forbid 3 5 6 (.system [[0,1,2,3,17,18,19,20,21,22,5,4],[7],[9],[12],[13],[16]]) (.forbid 3 6 1 (.system [[0,1,2,3,17,6,5,4],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 3 6 2 (.system [[0],[2,3,17,18,6,5,4],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 3 6 3 (.system [[0,1,2,3,17,18,19,6,5,4],[7],[9,10,11,12],[13],[16]]) (.forbid 3 6 4 (.system [[0],[2,3,17,18,19,20,6,5,4],[7],[9,10,11,12],[13],[16]]) (.forbid 3 6 5 (.system [[0,1,2,3,17,18,19,20,21,6,5,4],[7],[9],[12],[13],[16]]) (.forbid 3 6 6 (.system [[0],[2,3,17,18,19,20,21,22,6,5,4],[7],[9],[12],[13],[16]]) (.forbid 3 7 1 (.system [[0,1,2,3,17,7,6,5,4],[9,10,11,12],[13,14,15,16]]) (.forbid 3 8 1 (.system [[0],[2,3,17,8,7,6,5,4],[9,10,11,12],[13,14,15,16]]) (.forbid 3 8 2 (.system [[0,1,2,3,17,18,8,7,6,5,4],[9,10,11,12],[13],[16]]) (certificate_3067_part_1))))))))))))))))))))

noncomputable def certificate_3067_part_3 : FiniteCertificate := .forbid 1 4 1 (.system [[0,1,17,4,5,6,7,8,9,10,11,12],[2],[13,14,15,16]]) (.forbid 1 5 1 (.system [[0,1,17,5,4,3,2],[7,8,9,10,11,12],[13,14,15,16]]) (.forbid 1 5 2 (.system [[0,1,17,18,5,4,3,2],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 1 5 3 (.system [[0,1,17,18,19,5,4],[2],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 1 5 4 (.system [[0,1,17,18,19,20,5,4,3,2],[7],[9,10,11,12],[13],[16]]) (.forbid 1 5 5 (.system [[0,1,17,18,19,20,21,5,4],[2],[7],[9,10,11,12],[13],[16]]) (.forbid 1 5 6 (.system [[0,1,17,18,19,20,21,22,5,4,3,2],[7],[9],[12],[13],[16]]) (.forbid 1 6 1 (.system [[0,1,17,6,5,4,3,2],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 1 6 2 (.system [[0,1,17,18,6,5,4],[2],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 1 6 3 (.system [[0,1,17,18,19,6,5,4,3,2],[7],[9,10,11,12],[13],[16]]) (.forbid 1 6 4 (.system [[0,1,17,18,19,20,6,5,4],[2],[7],[9,10,11,12],[13],[16]]) (.forbid 1 6 5 (.system [[0,1,17,18,19,20,21,6,5,4,3,2],[7],[9],[12],[13],[16]]) (.forbid 1 6 6 (.system [[0,1,17,18,19,20,21,22,6,5,4],[2],[7],[9],[12],[13],[16]]) (.forbid 1 7 1 (.system [[0,1,17,7,6,5,4,3,2],[9,10,11,12],[13,14,15,16]]) (.forbid 1 8 1 (.system [[0,1,17,8,7,6,5,4],[2],[9,10,11,12],[13,14,15,16]]) (.forbid 1 8 2 (.system [[0,1,17,18,8,7,6,5,4,3,2],[9,10,11,12],[13],[16]]) (.forbid 1 8 3 (.system [[0,1,17,18,19,8,7,6,5,4],[2],[9,10,11,12],[13],[16]]) (.forbid 1 8 4 (.system [[0,1,17,18,19,20,8,7,6,5,4,3,2],[9],[12],[13],[16]]) (.forbid 1 8 5 (.system [[0,1,17,18,19,20,21,8,7,6,5,4],[2],[9],[12],[13],[16]]) (.forbid 1 8 6 (.system [[0,1,17,18,19,20,21,22,8,7],[2,3,4],[9],[12],[13],[16]]) (certificate_3067_part_2))))))))))))))))))))

noncomputable def certificate_3067_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[0,17,18,19,6,5,4],[2],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 6 4 (.system [[2,1,0,17,18,19,20,6,5,4],[7],[9,10,11,12],[13],[16]]) (.forbid 0 6 5 (.system [[0,17,18,19,20,21,6,5,4],[2],[7],[9,10,11,12],[13],[16]]) (.forbid 0 6 6 (.system [[2,1,0,17,18,19,20,21,22,6,5,4],[7],[9],[12],[13],[16]]) (.forbid 0 8 1 (.system [[2,1,0,17,8,7,6,5,4],[9,10,11,12],[13,14,15,16]]) (.forbid 0 8 2 (.system [[0,17,18,8,7,6,5,4],[2],[9,10,11,12],[13,14,15,16]]) (.forbid 0 8 3 (.system [[2,1,0,17,18,19,8,7,6,5,4],[9,10,11,12],[13],[16]]) (.forbid 0 8 4 (.system [[0,17,18,19,20,8,7,6,5,4],[2],[9,10,11,12],[13],[16]]) (.forbid 0 8 5 (.system [[2,1,0,17,18,19,20,21,8,7,6,5,4],[9],[12],[13],[16]]) (.forbid 0 8 6 (.system [[0,17,18,19,20,21,22,8,7,6,5,4],[2],[9],[12],[13],[16]]) (.forbid 0 10 1 (.system [[7,6,5,4,3,2,1,0,17,10,11,12],[9],[13,14,15,16]]) (.forbid 0 11 1 (.system [[7,6,5,4,3,2,1,0,17,11,10,9],[12],[13,14,15,16]]) (.forbid 0 13 1 (.system [[12,11,10,9,8,7,6,5,4,3,2,1,0,17,13,14,15,16]]) (.forbid 1 2 1 (.system [[0,1,17,2,3,4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 1 3 1 (.system [[0,1,17,3,2],[4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 1 3 2 (.system [[0,1,17,18,3,2],[4,5,6,7,8,9,10,11,12],[13],[16]]) (.forbid 1 3 3 (.system [[0,1,17,18,19,3,2],[4,5,6,7],[9,10,11,12],[13],[16]]) (.forbid 1 3 4 (.system [[0,1,17,18,19,20,3,2],[4,5,6,7,8,9],[12],[13],[16]]) (.forbid 1 3 5 (.system [[0,1,17,18,19,20,21,3,2],[4,5,6,7],[9],[12],[13],[16]]) (.forbid 1 3 6 (.system [[0,1,17,18,19,20,21,22,3,2],[4,5,6,7],[9],[12],[13],[16]]) (certificate_3067_part_3))))))))))))))))))))

noncomputable def certificate_3067 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2,3,4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 1 2 (.system [[0,17,18,1,2],[4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1,2,3,4,5,6,7],[9,10,11,12],[13],[16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1,2],[4,5,6,7],[9,10,11,12],[13],[16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2,3,4,5,6,7],[9],[12],[13],[16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1,2],[4,5,6,7],[9],[12],[13],[16]]) (.forbid 0 3 1 (.system [[0,17,3,2],[4,5,6,7,8,9,10,11,12],[13,14,15,16]]) (.forbid 0 3 2 (.system [[0,17,18,3,2],[4,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 3 3 (.system [[0,17,18,19,3,2],[4,5,6,7,8,9,10,11,12],[13],[16]]) (.forbid 0 3 4 (.system [[0,17,18,19,20,3,2],[4,5,6,7],[9,10,11,12],[13],[16]]) (.forbid 0 3 5 (.system [[0,17,18,19,20,21,3,2],[4,5,6,7,8,9],[12],[13],[16]]) (.forbid 0 3 6 (.system [[0,17,18,19,20,21,22,3,2],[4,5,6,7],[9],[12],[13],[16]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,17,5,6,7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 5 2 (.system [[2,1,0,17,18,5,4],[7,8,9,10,11,12],[13,14,15,16]]) (.forbid 0 5 3 (.system [[2,1,0,17,18,19,5,4],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 5 4 (.system [[0,17,18,19,20,5,4],[2],[7],[9,10,11,12],[13,14,15,16]]) (.forbid 0 5 5 (.system [[2,1,0,17,18,19,20,21,5,4],[7],[9,10,11,12],[13],[16]]) (.forbid 0 5 6 (.system [[0,17,18,19,20,21,22,5,4],[2],[7],[9,10,11,12],[13],[16]]) (.forbid 0 6 1 (.system [[2,1,0,17,6,5,4],[7,8,9,10,11,12],[13,14,15,16]]) (.forbid 0 6 2 (.system [[2,1,0,17,18,6,5,4],[7],[9,10,11,12],[13,14,15,16]]) (certificate_3067_part_4))))))))))))))))))))

noncomputable def certificate_3068_part_1 : FiniteCertificate := .forbid 3 8 3 (.system [[0],[2,3,17,18,19,8,7,6,5,4],[9,10,11,12],[14],[16]]) (.forbid 3 8 4 (.system [[0,1,2,3,17,18,19,20,8,7,6,5,4],[9],[12],[14],[16]]) (.forbid 3 8 5 (.system [[0],[2,3,17,18,19,20,21,8,7,6,5,4],[9],[12],[14],[16]]) (.forbid 3 8 6 (.system [[0,1,2,3,17,18,19,20,21,22,8,7],[4],[9],[12],[14],[16]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,17,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 4 8 1 (.system [[0,1,2],[7,6,5,4,17,8,9,10,11,12,13,14,15,16]]) (.forbid 5 6 1 (.system [[0,1,2,3,4,5,17,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 5 6 2 (.system [[0,1,2,3,4,5,17,18,6,7,8,9,10,11,12],[14],[16]]) (.forbid 5 6 3 (.system [[0,1,2,3,4,5,17,18,19,6,7],[9,10,11,12],[14],[16]]) (.forbid 5 6 4 (.system [[0,1,2],[4,5,17,18,19,20,6,7],[9,10,11,12],[14],[16]]) (.forbid 5 6 5 (.system [[0],[2],[4,5,17,18,19,20,21,6,7],[9,10,11,12],[14],[16]]) (.forbid 5 6 6 (.system [[0,1,2],[4,5,17,18,19,20,21,22,6,7],[9],[12],[14],[16]]) (.forbid 5 8 1 (.system [[0,1,2,3,4,5,17,8,7],[9,10,11,12,13,14,15,16]]) (.forbid 5 8 2 (.system [[0,1,2,3,4,5,17,18,8,7],[9,10,11,12,13,14],[16]]) (.forbid 5 8 3 (.system [[0,1,2,3,4,5,17,18,19,8,7],[9,10,11,12],[14],[16]]) (.forbid 5 8 4 (.system [[0,1,2],[4,5,17,18,19,20,8,7],[9,10,11,12],[14],[16]]) (.forbid 5 8 5 (.system [[0],[2],[4,5,17,18,19,20,21,8,7],[9,10,11,12],[14],[16]]) (.forbid 5 8 6 (.system [[0,1,2],[4,5,17,18,19,20,21,22,8,7],[9],[12],[14],[16]]) (.forbid 5 9 1 (.system [[0,1,2,3,4],[7,6,5,17,9,10,11,12,13,14,15,16]]) (.forbid 6 7 1 (.system [[0,1,2,3,4,5,6,17,7,8,9,10,11,12,13,14],[16]]) (certificate_3068_part_0))))))))))))))))))))

noncomputable def certificate_3068_part_2 : FiniteCertificate := .forbid 2 3 1 (.system [[0,1,2,17,3,4,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 2 5 1 (.system [[0,1,2,17,5,6,7,8,9,10,11,12,13,14,15,16],[4]]) (.forbid 2 6 1 (.system [[0,1,2,17,6,5,4],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 2 8 1 (.system [[0,1,2,17,8,7,6,5,4],[9,10,11,12,13,14,15,16]]) (.forbid 3 4 1 (.system [[0,1,2,3,17,4,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 3 5 1 (.system [[0,1,2,3,17,5,4],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 3 5 2 (.system [[0,1,2,3,17,18,5,4],[7,8,9,10,11,12,13,14],[16]]) (.forbid 3 5 3 (.system [[0,1,2,3,17,18,19,5,4],[7,8,9,10,11,12],[14],[16]]) (.forbid 3 5 4 (.system [[0,1,2,3,17,18,19,20,5,4],[7],[9,10,11,12],[14],[16]]) (.forbid 3 5 5 (.system [[0],[2,3,17,18,19,20,21,5,4],[7],[9,10,11,12],[14],[16]]) (.forbid 3 5 6 (.system [[0,1,2,3,17,18,19,20,21,22,5,4],[7],[9],[12],[14],[16]]) (.forbid 3 6 1 (.system [[0,1,2,3,17,6,5,4],[7,8,9,10,11,12,13,14],[16]]) (.forbid 3 6 2 (.system [[0,1,2,3,17,18,6,5,4],[7,8,9,10,11,12],[14],[16]]) (.forbid 3 6 3 (.system [[0,1,2,3,17,18,19,6,5,4],[7],[9,10,11,12],[14],[16]]) (.forbid 3 6 4 (.system [[0],[2,3,17,18,19,20,6,5,4],[7],[9,10,11,12],[14],[16]]) (.forbid 3 6 5 (.system [[0,1,2,3,17,18,19,20,21,6,5,4],[7],[9],[12],[14],[16]]) (.forbid 3 6 6 (.system [[0],[2,3,17,18,19,20,21,22,6,5,4],[7],[9],[12],[14],[16]]) (.forbid 3 7 1 (.system [[0,1,2,3,17,7,6,5,4],[9,10,11,12,13,14,15,16]]) (.forbid 3 8 1 (.system [[0,1,2,3,17,8,7,6,5,4],[9,10,11,12,13,14],[16]]) (.forbid 3 8 2 (.system [[0,1,2,3,17,18,8,7,6,5,4],[9,10,11,12],[14],[16]]) (certificate_3068_part_1))))))))))))))))))))

noncomputable def certificate_3068_part_3 : FiniteCertificate := .forbid 1 4 1 (.system [[0,1,17,4,5,6,7,8,9,10,11,12,13,14,15,16],[2]]) (.forbid 1 5 1 (.system [[0,1,17,5,4,3,2],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 1 5 2 (.system [[0,1,17,18,5,4,3,2],[7,8,9,10,11,12,13,14],[16]]) (.forbid 1 5 3 (.system [[0,1,17,18,19,5,4,3,2],[7,8,9,10,11,12],[14],[16]]) (.forbid 1 5 4 (.system [[0,1,17,18,19,20,5,4,3,2],[7],[9,10,11,12],[14],[16]]) (.forbid 1 5 5 (.system [[0,1,17,18,19,20,21,5,4],[2],[7],[9,10,11,12],[14],[16]]) (.forbid 1 5 6 (.system [[0,1,17,18,19,20,21,22,5,4,3,2],[7],[9],[12],[14],[16]]) (.forbid 1 6 1 (.system [[0,1,17,6,5,4,3,2],[7,8,9,10,11,12,13,14],[16]]) (.forbid 1 6 2 (.system [[0,1,17,18,6,5,4,3,2],[7,8,9,10,11,12],[14],[16]]) (.forbid 1 6 3 (.system [[0,1,17,18,19,6,5,4,3,2],[7],[9,10,11,12],[14],[16]]) (.forbid 1 6 4 (.system [[0,1,17,18,19,20,6,5,4],[2],[7],[9,10,11,12],[14],[16]]) (.forbid 1 6 5 (.system [[0,1,17,18,19,20,21,6,5,4,3,2],[7],[9],[12],[14],[16]]) (.forbid 1 6 6 (.system [[0,1,17,18,19,20,21,22,6,5,4],[2],[7],[9],[12],[14],[16]]) (.forbid 1 7 1 (.system [[0,1,17,7,6,5,4,3,2],[9,10,11,12,13,14,15,16]]) (.forbid 1 8 1 (.system [[0,1,17,8,7,6,5,4,3,2],[9,10,11,12,13,14],[16]]) (.forbid 1 8 2 (.system [[0,1,17,18,8,7,6,5,4,3,2],[9,10,11,12],[14],[16]]) (.forbid 1 8 3 (.system [[0,1,17,18,19,8,7,6,5,4],[2],[9,10,11,12],[14],[16]]) (.forbid 1 8 4 (.system [[0,1,17,18,19,20,8,7,6,5,4,3,2],[9],[12],[14],[16]]) (.forbid 1 8 5 (.system [[0,1,17,18,19,20,21,8,7,6,5,4],[2],[9],[12],[14],[16]]) (.forbid 1 8 6 (.system [[0,1,17,18,19,20,21,22,8,7],[2,3,4],[9],[12],[14],[16]]) (certificate_3068_part_2))))))))))))))))))))

noncomputable def certificate_3068_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,17,18,19,6,5,4],[7,8,9,10,11,12],[14],[16]]) (.forbid 0 6 4 (.system [[2,1,0,17,18,19,20,6,5,4],[7],[9,10,11,12],[14],[16]]) (.forbid 0 6 5 (.system [[0,17,18,19,20,21,6,5,4],[2],[7],[9,10,11,12],[14],[16]]) (.forbid 0 6 6 (.system [[2,1,0,17,18,19,20,21,22,6,5,4],[7],[9],[12],[14],[16]]) (.forbid 0 8 1 (.system [[2,1,0,17,8,7,6,5,4],[9,10,11,12,13,14,15,16]]) (.forbid 0 8 2 (.system [[2,1,0,17,18,8,7,6,5,4],[9,10,11,12,13,14],[16]]) (.forbid 0 8 3 (.system [[2,1,0,17,18,19,8,7,6,5,4],[9,10,11,12],[14],[16]]) (.forbid 0 8 4 (.system [[0,17,18,19,20,8,7,6,5,4],[2],[9,10,11,12],[14],[16]]) (.forbid 0 8 5 (.system [[2,1,0,17,18,19,20,21,8,7,6,5,4],[9],[12],[14],[16]]) (.forbid 0 8 6 (.system [[0,17,18,19,20,21,22,8,7,6,5,4],[2],[9],[12],[14],[16]]) (.forbid 0 10 1 (.system [[9,8,7,6,5,4,3,2,1,0,17,10,11,12,13,14],[16]]) (.forbid 0 11 1 (.system [[7,6,5,4,3,2,1,0,17,11,10,9],[12,13,14,15,16]]) (.forbid 0 13 1 (.system [[7,6,5,4,3,2,1,0,17,13,12,11,10,9],[14,15,16]]) (.forbid 1 2 1 (.system [[0,1,17,2,3,4,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 1 3 1 (.system [[0,1,17,3,2],[4,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 1 3 2 (.system [[0,1,17,18,3,2],[4,5,6,7,8,9,10,11,12],[14],[16]]) (.forbid 1 3 3 (.system [[0,1,17,18,19,3,2],[4,5,6,7],[9,10,11,12],[14],[16]]) (.forbid 1 3 4 (.system [[0,1,17,18,19,20,3,2],[4,5,6,7,8,9],[12],[14],[16]]) (.forbid 1 3 5 (.system [[0,1,17,18,19,20,21,3,2],[4,5,6,7],[9],[12],[14],[16]]) (.forbid 1 3 6 (.system [[0,1,17,18,19,20,21,22,3,2],[4,5,6,7],[9],[12],[14],[16]]) (certificate_3068_part_3))))))))))))))))))))

noncomputable def certificate_3068 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 0 1 2 (.system [[0,17,18,1,2,3,4,5,6,7,8,9,10,11,12],[14],[16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1,2,3,4,5,6,7],[9,10,11,12],[14],[16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1,2],[4,5,6,7],[9,10,11,12],[14],[16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2,3,4,5,6,7],[9],[12],[14],[16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1,2],[4,5,6,7],[9],[12],[14],[16]]) (.forbid 0 3 1 (.system [[0,17,3,2],[4,5,6,7,8,9,10,11,12,13,14,15,16]]) (.forbid 0 3 2 (.system [[0,17,18,3,2],[4,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 0 3 3 (.system [[0,17,18,19,3,2],[4,5,6,7,8,9,10,11,12],[14],[16]]) (.forbid 0 3 4 (.system [[0,17,18,19,20,3,2],[4,5,6,7],[9,10,11,12],[14],[16]]) (.forbid 0 3 5 (.system [[0,17,18,19,20,21,3,2],[4,5,6,7,8,9],[12],[14],[16]]) (.forbid 0 3 6 (.system [[0,17,18,19,20,21,22,3,2],[4,5,6,7],[9],[12],[14],[16]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,17,5,6,7,8,9,10,11,12,13,14],[16]]) (.forbid 0 5 2 (.system [[2,1,0,17,18,5,4],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 0 5 3 (.system [[2,1,0,17,18,19,5,4],[7,8,9,10,11,12,13,14],[16]]) (.forbid 0 5 4 (.system [[2,1,0,17,18,19,20,5,4],[7,8,9,10,11,12],[14],[16]]) (.forbid 0 5 5 (.system [[2,1,0,17,18,19,20,21,5,4],[7],[9,10,11,12],[14],[16]]) (.forbid 0 5 6 (.system [[0,17,18,19,20,21,22,5,4],[2],[7],[9,10,11,12],[14],[16]]) (.forbid 0 6 1 (.system [[2,1,0,17,6,5,4],[7,8,9,10,11,12,13,14,15,16]]) (.forbid 0 6 2 (.system [[2,1,0,17,18,6,5,4],[7,8,9,10,11,12,13,14],[16]]) (certificate_3068_part_4))))))))))))))))))))

end CycleClique

end OAI
end


