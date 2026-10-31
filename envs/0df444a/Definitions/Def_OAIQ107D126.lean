-- Prove2me | Definitions.Def_OAIQ107D126
-- name    : OAIQ107D126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:47:52.192329+00:00
-- url     : https://prove2.me/theorems/4b4133bd-c2b8-4a64-b057-f478aa0fb9e8
-- title:
--   Definitions bundle OAIQ107D126 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 460 declarations of OpenAI's Lean: 460 definitions. The definitions and types are `OAI.CycleClique.certificate_1045`, `OAI.CycleClique.certificate_1045_part_1`, `OAI.CycleClique.certificate_1045_part_2`, `OAI.CycleClique.certificate_108`, `OAI.CycleClique.certificate_1097`, `OAI.CycleClique.certificate_1097_part_1`, `OAI.CycleClique.certificate_1097_part_2`, `OAI.CycleClique.certificate_10_part_10_M`, `OAI.CycleClique.certificate_10_part_11_M`, `OAI.CycleClique.certificate_10_part_12_M`, `OAI.CycleClique.certificate_10_part_13_M`, `OAI.CycleClique.certificate_10_part_1_M`, `OAI.CycleClique.certificate_10_part_2_M`, `OAI.CycleClique.certificate_10_part_3_M`, `OAI.CycleClique.certificate_10_part_4_M`, `OAI.CycleClique.certificate_10_part_5_M`, `OAI.CycleClique.certificate_10_part_6_M`, `OAI.CycleClique.certificate_10_part_7_M`, `OAI.CycleClique.certificate_10_part_8_M`, `OAI.CycleClique.certificate_10_part_9_M`, `OAI.CycleClique.certificate_1118`, `OAI.CycleClique.certificate_1118_part_2`, `OAI.CycleClique.certificate_112`, `OAI.CycleClique.certificate_1147`, `OAI.CycleClique.certificate_1147_part_1`, `OAI.CycleClique.certificate_1147_part_2`, `OAI.CycleClique.certificate_115`, `OAI.CycleClique.certificate_1159_part_100_M`, `OAI.CycleClique.certificate_1159_part_101_E`, `OAI.CycleClique.certificate_1159_part_101_M`, `OAI.CycleClique.certificate_1159_part_102_M`, `OAI.CycleClique.certificate_1159_part_103_M`, `OAI.CycleClique.certificate_1159_part_104_M`, `OAI.CycleClique.certificate_1159_part_105_M`, `OAI.CycleClique.certificate_1159_part_106_M`, `OAI.CycleClique.certificate_1159_part_107_M`, `OAI.CycleClique.certificate_1159_part_108_M`, `OAI.CycleClique.certificate_1159_part_109_M`, `OAI.CycleClique.certificate_1159_part_10_M`, `OAI.CycleClique.certificate_1159_part_110_M` and 420 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates004`, `Ramsey_CycleClique_Certificates005`, `Ramsey_CycleClique_Certificates033`, `Ramsey_CycleClique_Certificates035`, `Ramsey_CycleClique_Certificates036`, `Ramsey_CycleClique_Certificates037`, `Ramsey_CycleClique_Certificates038`, `Ramsey_CycleClique_Certificates039`, `Ramsey_CycleClique_Certificates040`, `Ramsey_CycleClique_Certificates041`, `Ramsey_CycleClique_Certificates042`, `Ramsey_CycleClique_Certificates043`.
--
--   **Imports.** It imports the bundles `OAIQ107D008`, `OAIQ107D009`, `OAIQ107D010`, `OAIQ107D011`, `OAIQ107D012`, `OAIQ107D013`, `OAIQ107D014`, `OAIQ107D015`, `OAIQ107D016`, `OAIQ107D017`, `OAIQ107D018`, `OAIQ107D019`, `OAIQ107D020`, `OAIQ107D021`, `OAIQ107D022`, `OAIQ107D023` and `OAIQ107D048` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ107D134`; the proofs of `OAI.CycleClique.finite_patterns_14_8`, `OAI.CycleClique.patterns_15_7_0_verified`, `OAI.CycleClique.patterns_15_7_1_verified` and `OAI.CycleClique.patterns_15_7_4_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ107D008
import Definitions.Def_OAIQ107D009
import Definitions.Def_OAIQ107D010
import Definitions.Def_OAIQ107D011
import Definitions.Def_OAIQ107D012
import Definitions.Def_OAIQ107D013
import Definitions.Def_OAIQ107D014
import Definitions.Def_OAIQ107D015
import Definitions.Def_OAIQ107D016
import Definitions.Def_OAIQ107D017
import Definitions.Def_OAIQ107D018
import Definitions.Def_OAIQ107D019
import Definitions.Def_OAIQ107D020
import Definitions.Def_OAIQ107D021
import Definitions.Def_OAIQ107D022
import Definitions.Def_OAIQ107D023
import Definitions.Def_OAIQ107D048

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_10_part_1_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,1) :: (certificate_10_M))))))))))))))))

noncomputable def certificate_10_part_2_M : ForbiddenMatrix := ((2,4,0) :: (((1,4,0) :: (((0,4,0) :: (((0,2,0) :: (((2,4,2) :: (((0,5,1) :: (((0,4,4) :: (certificate_10_part_1_M))))))))))))))

noncomputable def certificate_10_part_3_M : ForbiddenMatrix := ((0,5,5) :: (((0,5,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((2,4,2) :: (((0,5,1) :: (((0,4,4) :: (certificate_10_part_1_M))))))))))))))))

noncomputable def certificate_10_part_4_M : ForbiddenMatrix := ((2,4,1) :: (((2,4,0) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,4,0) :: (((3,4,1) :: (certificate_10_part_3_M))))))))))))))

noncomputable def certificate_10_part_5_M : ForbiddenMatrix := ((0,3,4) :: (((4,5,2) :: (((4,5,1) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (((3,4,1) :: (certificate_10_part_3_M))))))))))))))

noncomputable def certificate_10_part_6_M : ForbiddenMatrix := ((0,1,4) :: (((0,2,0) :: (((4,5,2) :: (((4,5,1) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (((3,4,1) :: (certificate_10_part_3_M))))))))))))))))

noncomputable def certificate_10_part_7_M : ForbiddenMatrix := ((1,4,1) :: (((0,1,3) :: (((0,1,2) :: (((1,4,3) :: (((1,2,2) :: (((1,2,1) :: (((0,1,5) :: (certificate_10_part_6_M))))))))))))))

noncomputable def certificate_10_part_8_M : ForbiddenMatrix := ((0,6,2) :: (((0,6,1) :: (((0,3,0) :: (((1,4,3) :: (((1,2,2) :: (((1,2,1) :: (((0,1,5) :: (certificate_10_part_6_M))))))))))))))

noncomputable def certificate_10_part_9_M : ForbiddenMatrix := ((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((0,3,0) :: (((1,4,3) :: (((1,2,2) :: (((1,2,1) :: (((0,1,5) :: (certificate_10_part_6_M))))))))))))))))

noncomputable def certificate_10_part_10_M : ForbiddenMatrix := ((1,3,0) :: (((3,4,2) :: (((2,4,4) :: (((2,4,3) :: (((2,3,2) :: (((0,4,0) :: (((2,3,1) :: (certificate_10_part_9_M))))))))))))))

noncomputable def certificate_10_part_11_M : ForbiddenMatrix := ((2,4,0) :: (((1,3,0) :: (((3,4,2) :: (((2,4,4) :: (((2,4,3) :: (((2,3,2) :: (((0,4,0) :: (((2,3,1) :: (certificate_10_part_9_M))))))))))))))))

noncomputable def certificate_10_part_12_M : ForbiddenMatrix := ((1,6,0) :: (((1,4,0) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,6,0) :: (certificate_10_part_11_M))))))))))))))

noncomputable def certificate_10_part_13_M : ForbiddenMatrix := ((2,5,0) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,6,0) :: (((2,5,1) :: (certificate_10_part_11_M))))))))))))))

noncomputable def certificate_11_part_1_M : ForbiddenMatrix := ((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,5) :: (((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (certificate_11_M))))))))))))))))

noncomputable def certificate_12_part_1_M : ForbiddenMatrix := ((0,5,2) :: (((0,5,1) :: (((0,3,1) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_12_M))))))))))))))))

noncomputable def certificate_12_part_2_M : ForbiddenMatrix := ((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((1,2,1) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (certificate_12_part_1_M))))))))))))))))

noncomputable def certificate_12_part_1 : FiniteCertificate := .forbid 0 5 3 (.system [[0,6,7,8,5],[2]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[2]]) (.forbid 0 5 5 (.system [[0,6,7,8,9,10,5],[2]]) (.forbid 1 2 1 (.system [[0,1,6,2,3,4,5]]) (.forbid 1 5 1 (.system [[0,1,6,5,4,3,2]]) (.forbid 1 5 2 (.system [[0,1,6,7,5],[2]]) (.forbid 1 5 3 (.system [[0,1,6,7,8,5],[2]]) (.forbid 1 5 4 (.system [[0,1,6,7,8,9,5],[2]]) (certificate_12_part_2))))))))

noncomputable def certificate_12 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1,2],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1,2],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1,2],[5]]) (.forbid 0 1 5 (.cycle [0,1,10,9,8,7,6]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[2]]) (.forbid 0 5 1 (.cycle [0,1,2,3,4,5,6]) (.forbid 0 5 2 (.system [[0,6,7,5,4,3,2]]) (certificate_12_part_1))))))))

noncomputable def certificate_25_part_12_E : List (ℕ × ℕ) := certificate_25_part_11_E

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_108 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1],[2],[3,4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1],[2],[3,4,5,6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1],[2],[3],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[2],[3],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[2],[3],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[2],[3],[6]]) (.forbid 0 2 1 (.system [[0,7,2],[1],[3,4,5,6]]) (.forbid 0 2 2 (.system [[0,7,8,2],[1],[3,4,5,6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2],[1],[3],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2],[1],[3],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2],[1],[3],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2],[1],[3],[6]]) (.forbid 0 3 1 (.system [[0,7,3,4,5,6],[1],[2]]) (.forbid 0 3 2 (.system [[0,7,8,3,4,5,6],[1],[2]]) (.forbid 0 3 3 (.system [[0,7,8,9,3],[1],[2],[6]]) (.forbid 0 3 4 (.system [[0,7,8,9,10,3],[1],[2],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3],[1],[2],[6]]) (.forbid 0 3 6 (.system [[0,7,8,9,10,11,12,3],[1],[2],[6]]) (.forbid 1 2 1 (.system [[0],[1,7,2],[3,4,5,6]]) (.forbid 1 2 2 (.system [[0],[1,7,8,2],[3,4,5,6]]) (certificate_108_part_0))))))))))))))))))))

noncomputable def certificate_112 : FiniteCertificate := .forbid 0 1 1 (.system [[0,8,1],[2,3,4,5,6,7]]) (.forbid 0 1 2 (.system [[0,8,9,1],[2],[4,5,6,7]]) (.forbid 0 1 3 (.system [[0,8,9,10,1],[2],[4],[7]]) (.forbid 0 1 4 (.system [[0,8,9,10,11,1],[2],[4],[7]]) (.forbid 0 1 5 (.system [[0,8,9,10,11,12,1],[2],[4],[7]]) (.forbid 0 1 6 (.system [[0,8,9,10,11,12,13,1],[2],[4],[7]]) (.forbid 0 2 1 (.system [[0,8,2,3,4,5,6,7],[1]]) (.forbid 0 2 2 (.system [[0,8,9,2],[1],[4,5,6,7]]) (.forbid 0 2 3 (.system [[0,8,9,10,2],[1],[4],[7]]) (.forbid 0 2 4 (.system [[0,8,9,10,11,2],[1],[4],[7]]) (.forbid 0 2 5 (.system [[0,8,9,10,11,12,2],[1],[4],[7]]) (.forbid 0 2 6 (.system [[0,8,9,10,11,12,13,2],[1],[4],[7]]) (.forbid 0 3 1 (.system [[0,8,3,2],[1],[4,5,6,7]]) (.forbid 0 3 2 (.system [[0,8,9,3,2],[1],[4],[7]]) (.forbid 0 3 3 (.system [[0,8,9,10,3,2],[1],[4],[7]]) (.forbid 0 3 4 (.system [[0,8,9,10,11,3,2],[1],[4],[7]]) (.forbid 0 3 5 (.system [[0,8,9,10,11,12,3,2],[1],[4],[7]]) (.forbid 0 3 6 (.system [[0,8,9,10,11,12,13,3,2],[1],[4],[7]]) (.forbid 0 5 1 (.system [[0,8,5,6,7],[1],[2],[4]]) (.forbid 1 2 1 (.system [[0],[1,8,2,3,4,5,6,7]]) (certificate_112_part_0))))))))))))))))))))

noncomputable def certificate_115 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1,2,3],[4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1],[3],[4],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1],[3],[4],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[3],[4],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[3],[4],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[3],[4],[6]]) (.forbid 0 2 1 (.system [[0,7,2,1],[3],[4],[6]]) (.forbid 0 2 2 (.system [[0,7,8,2,1],[3],[4],[6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2,1],[3],[4],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2,1],[3],[4],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2,1],[3],[4],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2,1],[3],[4],[6]]) (.forbid 0 4 1 (.system [[0,7,4,5,6],[1,2,3]]) (.forbid 0 4 2 (.system [[0,7,8,4],[1],[3],[6]]) (.forbid 0 4 3 (.system [[0,7,8,9,4],[1],[3],[6]]) (.forbid 0 4 4 (.system [[0,7,8,9,10,4],[1],[3],[6]]) (.forbid 0 4 5 (.system [[0,7,8,9,10,11,4],[1],[3],[6]]) (.forbid 0 4 6 (.system [[0,7,8,9,10,11,12,4],[1],[3],[6]]) (.forbid 1 2 1 (.system [[0],[1,7,2,3],[4],[6]]) (.forbid 1 2 2 (.system [[0],[1,7,8,2,3],[4],[6]]) (certificate_115_part_0))))))))))))))))))))

noncomputable def certificate_117_part_1 : FiniteCertificate := .forbid 1 2 1 (.system [[0],[1,9,2,3],[4,5,6,7,8]]) (.forbid 1 2 2 (.system [[0],[1,9,10,2,3],[4,5,6,7,8]]) (.forbid 1 2 3 (.system [[0],[1,9,10,11,2,3],[4],[8]]) (.forbid 1 2 4 (.system [[0],[1,9,10,11,12,2,3],[4],[8]]) (.forbid 1 2 5 (.system [[0],[1,9,10,11,12,13,2,3],[4],[8]]) (.forbid 1 2 6 (.system [[0],[1,9,10,11,12,13,14,2,3],[4],[8]]) (.forbid 1 4 1 (.system [[0],[3,2,1,9,4,5,6,7,8]]) (.forbid 1 4 2 (.system [[0],[1,9,10,4,5,6,7,8],[3]]) (.forbid 1 4 3 (.system [[0],[1,9,10,11,4,5,6,7,8],[3]]) (.forbid 1 4 4 (.system [[0],[1,9,10,11,12,4],[3],[8]]) (.forbid 1 4 5 (.system [[0],[1,9,10,11,12,13,4],[3],[8]]) (.forbid 1 4 6 (.system [[0],[1,9,10,11,12,13,14,4],[3],[8]]) (.forbid 1 5 1 (.system [[0],[1,9,5,6,7,8],[3],[4]]) (.forbid 1 7 1 (.system [[0],[1,9,7,6,5,4],[3],[8]]) (.forbid 2 3 1 (.system [[0],[1,2,9,3],[4,5,6,7,8]]) (.forbid 2 4 1 (.system [[0],[1,2,9,4,5,6,7,8],[3]]) (.forbid 2 4 2 (.system [[0],[1,2,9,10,4,5,6,7,8],[3]]) (.forbid 2 4 3 (.system [[0],[1,2,9,10,11,4],[3],[8]]) (.forbid 2 4 4 (.system [[0],[1,2,9,10,11,12,4],[3],[8]]) (.forbid 2 4 5 (.system [[0],[1,2,9,10,11,12,13,4],[3],[8]]) (certificate_117_part_0))))))))))))))))))))

noncomputable def certificate_117 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2,3],[4,5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1],[3],[4,5,6,7,8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1],[3],[4,5,6,7,8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1],[3],[4],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1],[3],[4],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[3],[4],[8]]) (.forbid 0 2 1 (.system [[0,9,2,1],[3],[4,5,6,7,8]]) (.forbid 0 2 2 (.system [[0,9,10,2,1],[3],[4,5,6,7,8]]) (.forbid 0 2 3 (.system [[0,9,10,11,2,1],[3],[4],[8]]) (.forbid 0 2 4 (.system [[0,9,10,11,12,2,1],[3],[4],[8]]) (.forbid 0 2 5 (.system [[0,9,10,11,12,13,2,1],[3],[4],[8]]) (.forbid 0 2 6 (.system [[0,9,10,11,12,13,14,2,1],[3],[4],[8]]) (.forbid 0 3 1 (.system [[0,9,3,2,1],[4,5,6,7,8]]) (.forbid 0 4 1 (.system [[0,9,4,5,6,7,8],[1,2,3]]) (.forbid 0 4 2 (.system [[0,9,10,4,5,6,7,8],[1],[3]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,5,6,7,8],[1],[3]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4],[1],[3],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4],[1],[3],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4],[1],[3],[8]]) (.forbid 0 5 1 (.system [[0,9,5,6,7,8],[1],[3],[4]]) (certificate_117_part_1))))))))))))))))))))

noncomputable def certificate_119_part_1 : FiniteCertificate := .forbid 1 2 1 (.system [[0],[1,9,2,3],[5,6,7,8]]) (.forbid 1 2 2 (.system [[0],[1,9,10,2,3,4,5],[8]]) (.forbid 1 2 3 (.system [[0],[1,9,10,11,2,3],[5],[8]]) (.forbid 1 2 4 (.system [[0],[1,9,10,11,12,2,3],[5],[8]]) (.forbid 1 2 5 (.system [[0],[1,9,10,11,12,13,2,3],[5],[8]]) (.forbid 1 2 6 (.system [[0],[1,9,10,11,12,13,14,2,3],[5],[8]]) (.forbid 1 4 1 (.system [[0],[1,9,4,3],[5,6,7,8]]) (.forbid 1 4 2 (.system [[0],[1,9,10,4,3],[5,6,7,8]]) (.forbid 1 4 3 (.system [[0],[1,9,10,11,4,3],[5],[8]]) (.forbid 1 4 4 (.system [[0],[1,9,10,11,12,4,3],[5],[8]]) (.forbid 1 4 5 (.system [[0],[1,9,10,11,12,13,4,3],[5],[8]]) (.forbid 1 4 6 (.system [[0],[1,9,10,11,12,13,14,4,3],[5],[8]]) (.forbid 1 6 1 (.system [[0],[3,2,1,9,6,7,8],[5]]) (.forbid 1 7 1 (.system [[0],[3,2,1,9,7,6,5],[8]]) (.forbid 2 3 1 (.system [[0],[1,2,9,3],[5,6,7,8]]) (.forbid 2 4 1 (.system [[0],[1,2,9,4,3],[5,6,7,8]]) (.forbid 2 4 2 (.system [[0],[1,2,9,10,4,3],[5],[8]]) (.forbid 2 4 3 (.system [[0],[1,2,9,10,11,4,3],[5],[8]]) (.forbid 2 4 4 (.system [[0],[1,2,9,10,11,12,4,3],[5],[8]]) (.forbid 2 4 5 (.system [[0],[1,2,9,10,11,12,13,4,3],[5],[8]]) (certificate_119_part_0))))))))))))))))))))

noncomputable def certificate_119 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2,3,4,5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1],[3],[5,6,7,8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1,2,3],[5],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1],[3],[5],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1],[3],[5],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[3],[5],[8]]) (.forbid 0 2 1 (.system [[0,9,2,1],[3],[5,6,7,8]]) (.forbid 0 2 2 (.system [[0,9,10,2,1],[3,4,5],[8]]) (.forbid 0 2 3 (.system [[0,9,10,11,2,1],[3],[5],[8]]) (.forbid 0 2 4 (.system [[0,9,10,11,12,2,1],[3],[5],[8]]) (.forbid 0 2 5 (.system [[0,9,10,11,12,13,2,1],[3],[5],[8]]) (.forbid 0 2 6 (.system [[0,9,10,11,12,13,14,2,1],[3],[5],[8]]) (.forbid 0 4 1 (.system [[0,9,4,3],[1],[5,6,7,8]]) (.forbid 0 4 2 (.system [[0,9,10,4,3,2,1],[5],[8]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,3],[1],[5],[8]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4,3],[1],[5],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4,3],[1],[5],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4,3],[1],[5],[8]]) (.forbid 0 6 1 (.system [[0,9,6,7,8],[1,2,3],[5]]) (.forbid 0 7 1 (.system [[0,9,7,6,5],[1,2,3],[8]]) (certificate_119_part_1))))))))))))))))))))

noncomputable def certificate_123_part_1 : FiniteCertificate := .forbid 1 2 1 (.system [[0,1,9,2],[3],[5,6,7,8]]) (.forbid 1 3 1 (.system [[0,1,9,3],[2],[5,6,7,8]]) (.forbid 1 3 2 (.system [[0,1,9,10,3,4,5],[2],[8]]) (.forbid 1 3 3 (.system [[0,1,9,10,11,3],[2],[5],[8]]) (.forbid 1 3 4 (.system [[0,1,9,10,11,12,3],[2],[5],[8]]) (.forbid 1 3 5 (.system [[0,1,9,10,11,12,13,3],[2],[5],[8]]) (.forbid 1 3 6 (.system [[0,1,9,10,11,12,13,14,3],[2],[5],[8]]) (.forbid 1 4 1 (.system [[0,1,9,4,3],[2],[5,6,7,8]]) (.forbid 1 4 2 (.system [[0,1,9,10,4,3],[2],[5],[8]]) (.forbid 1 4 3 (.system [[0,1,9,10,11,4,3],[2],[5],[8]]) (.forbid 1 4 4 (.system [[0,1,9,10,11,12,4,3],[2],[5],[8]]) (.forbid 1 4 5 (.system [[0,1,9,10,11,12,13,4,3],[2],[5],[8]]) (.forbid 1 4 6 (.system [[0,1,9,10,11,12,13,14,4,3],[2],[5],[8]]) (.forbid 1 5 1 (.system [[0,1,9,5,6,7,8],[2],[3]]) (.forbid 2 3 1 (.system [[0,1,2,9,3,4,5,6,7,8]]) (.forbid 2 4 1 (.system [[0],[2,9,4,3],[5,6,7,8]]) (.forbid 3 4 1 (.system [[0],[2],[3,9,4,5,6,7,8]]) (.forbid 3 4 2 (.system [[0,1,2],[3,9,10,4,5],[8]]) (.forbid 3 4 3 (.system [[0],[2],[3,9,10,11,4,5],[8]]) (.forbid 3 4 4 (.system [[0],[2],[3,9,10,11,12,4,5],[8]]) (certificate_123_part_0))))))))))))))))))))

noncomputable def certificate_123 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2],[3],[5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1,2],[3,4,5],[8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1,2],[3],[5],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1,2],[3],[5],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1,2],[3],[5],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1,2],[3],[5],[8]]) (.forbid 0 3 1 (.system [[2,1,0,9,3,4,5,6,7,8]]) (.forbid 0 3 2 (.system [[0,9,10,3],[2],[5,6,7,8]]) (.forbid 0 3 3 (.system [[2,1,0,9,10,11,3],[5],[8]]) (.forbid 0 3 4 (.system [[0,9,10,11,12,3],[2],[5],[8]]) (.forbid 0 3 5 (.system [[0,9,10,11,12,13,3],[2],[5],[8]]) (.forbid 0 3 6 (.system [[0,9,10,11,12,13,14,3],[2],[5],[8]]) (.forbid 0 4 1 (.system [[0,9,4,3],[2],[5,6,7,8]]) (.forbid 0 4 2 (.system [[2,1,0,9,10,4,3],[5],[8]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,3],[2],[5],[8]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4,3],[2],[5],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4,3],[2],[5],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4,3],[2],[5],[8]]) (.forbid 0 6 1 (.system [[2,1,0,9,6,7,8],[3],[5]]) (.forbid 0 7 1 (.system [[2,1,0,9,7,6,5],[3],[8]]) (certificate_123_part_1))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_128_part_1 : FiniteCertificate := .forbid 1 2 1 (.system [[0],[1,8,2],[3],[4,5,6,7]]) (.forbid 1 2 2 (.system [[0],[1,8,9,2],[3],[4,5,6,7]]) (.forbid 1 2 3 (.system [[0],[1,8,9,10,2],[3],[4],[7]]) (.forbid 1 2 4 (.system [[0],[1,8,9,10,11,2],[3],[4],[7]]) (.forbid 1 2 5 (.system [[0],[1,8,9,10,11,12,2],[3],[4],[7]]) (.forbid 1 2 6 (.system [[0],[1,8,9,10,11,12,13,2],[3],[4],[7]]) (.forbid 1 3 1 (.system [[0],[1,8,3],[2],[4,5,6,7]]) (.forbid 1 3 2 (.system [[0],[1,8,9,3],[2],[4,5,6,7]]) (.forbid 1 3 3 (.system [[0],[1,8,9,10,3],[2],[4],[7]]) (.forbid 1 3 4 (.system [[0],[1,8,9,10,11,3],[2],[4],[7]]) (.forbid 1 3 5 (.system [[0],[1,8,9,10,11,12,3],[2],[4],[7]]) (.forbid 1 3 6 (.system [[0],[1,8,9,10,11,12,13,3],[2],[4],[7]]) (.forbid 1 4 1 (.system [[0],[1,8,4,5,6,7],[2],[3]]) (.forbid 1 5 1 (.system [[0],[1,8,5,6,7],[2],[3],[4]]) (.forbid 2 3 1 (.system [[0],[1],[2,8,3],[4,5,6,7]]) (.forbid 2 3 2 (.system [[0],[1],[2,8,9,3],[4,5,6,7]]) (.forbid 2 3 3 (.system [[0],[1],[2,8,9,10,3],[4],[7]]) (.forbid 2 3 4 (.system [[0],[1],[2,8,9,10,11,3],[4],[7]]) (.forbid 2 3 5 (.system [[0],[1],[2,8,9,10,11,12,3],[4],[7]]) (.forbid 2 3 6 (.system [[0],[1],[2,8,9,10,11,12,13,3],[4],[7]]) (certificate_128_part_0))))))))))))))))))))

noncomputable def certificate_128 : FiniteCertificate := .forbid 0 1 1 (.system [[0,8,1],[2],[3],[4,5,6,7]]) (.forbid 0 1 2 (.system [[0,8,9,1],[2],[3],[4,5,6,7]]) (.forbid 0 1 3 (.system [[0,8,9,10,1],[2],[3],[4],[7]]) (.forbid 0 1 4 (.system [[0,8,9,10,11,1],[2],[3],[4],[7]]) (.forbid 0 1 5 (.system [[0,8,9,10,11,12,1],[2],[3],[4],[7]]) (.forbid 0 1 6 (.system [[0,8,9,10,11,12,13,1],[2],[3],[4],[7]]) (.forbid 0 2 1 (.system [[0,8,2],[1],[3],[4,5,6,7]]) (.forbid 0 2 2 (.system [[0,8,9,2],[1],[3],[4,5,6,7]]) (.forbid 0 2 3 (.system [[0,8,9,10,2],[1],[3],[4],[7]]) (.forbid 0 2 4 (.system [[0,8,9,10,11,2],[1],[3],[4],[7]]) (.forbid 0 2 5 (.system [[0,8,9,10,11,12,2],[1],[3],[4],[7]]) (.forbid 0 2 6 (.system [[0,8,9,10,11,12,13,2],[1],[3],[4],[7]]) (.forbid 0 3 1 (.system [[0,8,3],[1],[2],[4,5,6,7]]) (.forbid 0 3 2 (.system [[0,8,9,3],[1],[2],[4,5,6,7]]) (.forbid 0 3 3 (.system [[0,8,9,10,3],[1],[2],[4],[7]]) (.forbid 0 3 4 (.system [[0,8,9,10,11,3],[1],[2],[4],[7]]) (.forbid 0 3 5 (.system [[0,8,9,10,11,12,3],[1],[2],[4],[7]]) (.forbid 0 3 6 (.system [[0,8,9,10,11,12,13,3],[1],[2],[4],[7]]) (.forbid 0 4 1 (.system [[0,8,4,5,6,7],[1],[2],[3]]) (.forbid 0 5 1 (.system [[0,8,5,6,7],[1],[2],[3],[4]]) (certificate_128_part_1))))))))))))))))))))

noncomputable def certificate_133_part_1 : FiniteCertificate := .forbid 0 6 1 (.system [[0,9,6,7,8],[1],[2],[4],[5]]) (.forbid 1 2 1 (.system [[0],[1,9,2,3,4],[5,6,7,8]]) (.forbid 1 2 2 (.system [[0],[1,9,10,2],[4],[5,6,7,8]]) (.forbid 1 2 3 (.system [[0],[1,9,10,11,2],[4],[5],[8]]) (.forbid 1 2 4 (.system [[0],[1,9,10,11,12,2],[4],[5],[8]]) (.forbid 1 2 5 (.system [[0],[1,9,10,11,12,13,2],[4],[5],[8]]) (.forbid 1 2 6 (.system [[0],[1,9,10,11,12,13,14,2],[4],[5],[8]]) (.forbid 1 3 1 (.system [[0],[1,9,3,2],[4],[5,6,7,8]]) (.forbid 1 3 2 (.system [[0],[1,9,10,3,2],[4],[5],[8]]) (.forbid 1 3 3 (.system [[0],[1,9,10,11,3,2],[4],[5],[8]]) (.forbid 1 3 4 (.system [[0],[1,9,10,11,12,3,2],[4],[5],[8]]) (.forbid 1 3 5 (.system [[0],[1,9,10,11,12,13,3,2],[4],[5],[8]]) (.forbid 1 3 6 (.system [[0],[1,9,10,11,12,13,14,3,2],[4],[5],[8]]) (.forbid 1 4 1 (.system [[0],[1,9,4,3,2],[5,6,7,8]]) (.forbid 1 5 1 (.system [[0],[1,9,5,6,7,8],[2,3,4]]) (.forbid 1 6 1 (.system [[0],[1,9,6,7,8],[2],[4],[5]]) (.forbid 2 3 1 (.system [[0],[1],[2,9,3,4],[5,6,7,8]]) (.forbid 2 3 2 (.system [[0],[1],[2,9,10,3,4],[5],[8]]) (.forbid 2 3 3 (.system [[0],[1],[2,9,10,11,3,4],[5],[8]]) (.forbid 2 3 4 (.system [[0],[1],[2,9,10,11,12,3,4],[5],[8]]) (certificate_133_part_0))))))))))))))))))))

noncomputable def certificate_133 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1],[2,3,4],[5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1],[2],[4],[5,6,7,8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1],[2],[4],[5],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1],[2],[4],[5],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1],[2],[4],[5],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[2],[4],[5],[8]]) (.forbid 0 2 1 (.system [[0,9,2,3,4],[1],[5,6,7,8]]) (.forbid 0 2 2 (.system [[0,9,10,2],[1],[4],[5,6,7,8]]) (.forbid 0 2 3 (.system [[0,9,10,11,2],[1],[4],[5],[8]]) (.forbid 0 2 4 (.system [[0,9,10,11,12,2],[1],[4],[5],[8]]) (.forbid 0 2 5 (.system [[0,9,10,11,12,13,2],[1],[4],[5],[8]]) (.forbid 0 2 6 (.system [[0,9,10,11,12,13,14,2],[1],[4],[5],[8]]) (.forbid 0 3 1 (.system [[0,9,3,2],[1],[4],[5,6,7,8]]) (.forbid 0 3 2 (.system [[0,9,10,3,2],[1],[4],[5],[8]]) (.forbid 0 3 3 (.system [[0,9,10,11,3,2],[1],[4],[5],[8]]) (.forbid 0 3 4 (.system [[0,9,10,11,12,3,2],[1],[4],[5],[8]]) (.forbid 0 3 5 (.system [[0,9,10,11,12,13,3,2],[1],[4],[5],[8]]) (.forbid 0 3 6 (.system [[0,9,10,11,12,13,14,3,2],[1],[4],[5],[8]]) (.forbid 0 4 1 (.system [[0,9,4,3,2],[1],[5,6,7,8]]) (.forbid 0 5 1 (.system [[0,9,5,6,7,8],[1],[2,3,4]]) (certificate_133_part_1))))))))))))))))))))

noncomputable def certificate_135_part_1 : FiniteCertificate := .forbid 0 7 1 (.system [[0,9,7,6],[1,2,3],[4],[8]]) (.forbid 1 2 1 (.system [[0],[1,9,2,3],[4,5,6],[8]]) (.forbid 1 2 2 (.system [[0],[1,9,10,2,3],[4],[6],[8]]) (.forbid 1 2 3 (.system [[0],[1,9,10,11,2,3],[4],[6],[8]]) (.forbid 1 2 4 (.system [[0],[1,9,10,11,12,2,3],[4],[6],[8]]) (.forbid 1 2 5 (.system [[0],[1,9,10,11,12,13,2,3],[4],[6],[8]]) (.forbid 1 2 6 (.system [[0],[1,9,10,11,12,13,14,2,3],[4],[6],[8]]) (.forbid 1 4 1 (.system [[0],[3,2,1,9,4,5,6,7,8]]) (.forbid 1 4 2 (.system [[0],[3,2,1,9,10,4],[6],[8]]) (.forbid 1 4 3 (.system [[0],[1,9,10,11,4],[3],[6],[8]]) (.forbid 1 4 4 (.system [[0],[1,9,10,11,12,4],[3],[6],[8]]) (.forbid 1 4 5 (.system [[0],[1,9,10,11,12,13,4],[3],[6],[8]]) (.forbid 1 4 6 (.system [[0],[1,9,10,11,12,13,14,4],[3],[6],[8]]) (.forbid 1 5 1 (.system [[0],[3,2,1,9,5,4],[6],[8]]) (.forbid 1 7 1 (.system [[0],[3,2,1,9,7,6],[4],[8]]) (.forbid 1 8 1 (.system [[0],[3,2,1,9,8,7,6,5,4]]) (.forbid 2 3 1 (.system [[0],[1,2,9,3],[4,5,6],[8]]) (.forbid 2 4 1 (.system [[0],[1,2,9,4,5,6],[3],[8]]) (.forbid 2 4 2 (.system [[0],[1,2,9,10,4],[3],[6],[8]]) (.forbid 2 4 3 (.system [[0],[1,2,9,10,11,4],[3],[6],[8]]) (certificate_135_part_0))))))))))))))))))))

noncomputable def certificate_135 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2,3],[4,5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1,2,3],[4],[6],[8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1],[3],[4],[6],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1],[3],[4],[6],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1],[3],[4],[6],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[3],[4],[6],[8]]) (.forbid 0 2 1 (.system [[0,9,2,1],[3],[4,5,6],[8]]) (.forbid 0 2 2 (.system [[0,9,10,2,1],[3],[4],[6],[8]]) (.forbid 0 2 3 (.system [[0,9,10,11,2,1],[3],[4],[6],[8]]) (.forbid 0 2 4 (.system [[0,9,10,11,12,2,1],[3],[4],[6],[8]]) (.forbid 0 2 5 (.system [[0,9,10,11,12,13,2,1],[3],[4],[6],[8]]) (.forbid 0 2 6 (.system [[0,9,10,11,12,13,14,2,1],[3],[4],[6],[8]]) (.forbid 0 3 1 (.system [[0,9,3,2,1],[4,5,6,7,8]]) (.forbid 0 4 1 (.system [[0,9,4,5,6,7,8],[1,2,3]]) (.forbid 0 4 2 (.system [[0,9,10,4],[1,2,3],[6],[8]]) (.forbid 0 4 3 (.system [[0,9,10,11,4],[1],[3],[6],[8]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4],[1],[3],[6],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4],[1],[3],[6],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4],[1],[3],[6],[8]]) (.forbid 0 5 1 (.system [[0,9,5,4],[1,2,3],[6],[8]]) (certificate_135_part_1))))))))))))))))))))

noncomputable def certificate_136_part_1 : FiniteCertificate := .forbid 0 7 1 (.system [[2,1,0,9,7,6],[3],[5],[8]]) (.forbid 1 2 1 (.system [[0,1,9,2],[3,4,5],[6],[8]]) (.forbid 1 3 1 (.system [[0,1,9,3,4,5],[2],[6],[8]]) (.forbid 1 3 2 (.system [[0,1,9,10,3],[2],[5],[6],[8]]) (.forbid 1 3 3 (.system [[0,1,9,10,11,3],[2],[5],[6],[8]]) (.forbid 1 3 4 (.system [[0,1,9,10,11,12,3],[2],[5],[6],[8]]) (.forbid 1 3 5 (.system [[0,1,9,10,11,12,13,3],[2],[5],[6],[8]]) (.forbid 1 3 6 (.system [[0,1,9,10,11,12,13,14,3],[2],[5],[6],[8]]) (.forbid 1 4 1 (.system [[0,1,9,4,3],[2],[5],[6],[8]]) (.forbid 1 4 2 (.system [[0,1,9,10,4,3],[2],[5],[6],[8]]) (.forbid 1 4 3 (.system [[0,1,9,10,11,4,3],[2],[5],[6],[8]]) (.forbid 1 4 4 (.system [[0,1,9,10,11,12,4,3],[2],[5],[6],[8]]) (.forbid 1 4 5 (.system [[0,1,9,10,11,12,13,4,3],[2],[5],[6],[8]]) (.forbid 1 4 6 (.system [[0,1,9,10,11,12,13,14,4,3],[2],[5],[6],[8]]) (.forbid 1 5 1 (.system [[0,1,9,5,4,3],[2],[6],[8]]) (.forbid 1 6 1 (.system [[0,1,9,6],[2],[3,4,5],[8]]) (.forbid 2 3 1 (.system [[0,1,2,9,3,4,5],[6,7,8]]) (.forbid 2 4 1 (.system [[0,1,2,9,4,3],[5],[6],[8]]) (.forbid 3 4 1 (.system [[0,1,2],[3,9,4,5],[6],[8]]) (.forbid 3 4 2 (.system [[0],[2],[3,9,10,4,5],[6],[8]]) (certificate_136_part_0))))))))))))))))))))

noncomputable def certificate_136 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2],[3,4,5],[6],[8]]) (.forbid 0 1 2 (.system [[0,9,10,1,2],[3],[5],[6],[8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1,2],[3],[5],[6],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1,2],[3],[5],[6],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1,2],[3],[5],[6],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1,2],[3],[5],[6],[8]]) (.forbid 0 3 1 (.system [[2,1,0,9,3,4,5],[6,7,8]]) (.forbid 0 3 2 (.system [[2,1,0,9,10,3],[5],[6],[8]]) (.forbid 0 3 3 (.system [[0,9,10,11,3],[2],[5],[6],[8]]) (.forbid 0 3 4 (.system [[0,9,10,11,12,3],[2],[5],[6],[8]]) (.forbid 0 3 5 (.system [[0,9,10,11,12,13,3],[2],[5],[6],[8]]) (.forbid 0 3 6 (.system [[0,9,10,11,12,13,14,3],[2],[5],[6],[8]]) (.forbid 0 4 1 (.system [[2,1,0,9,4,3],[5],[6],[8]]) (.forbid 0 4 2 (.system [[0,9,10,4,3],[2],[5],[6],[8]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,3],[2],[5],[6],[8]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4,3],[2],[5],[6],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4,3],[2],[5],[6],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4,3],[2],[5],[6],[8]]) (.forbid 0 5 1 (.system [[2,1,0,9,5,4,3],[6,7,8]]) (.forbid 0 6 1 (.system [[2,1,0,9,6,7,8],[3,4,5]]) (certificate_136_part_1))))))))))))))))))))

noncomputable def certificate_137_part_1 : FiniteCertificate := .forbid 1 2 1 (.system [[0],[1,7,2],[3],[4],[5],[6]]) (.forbid 1 2 2 (.system [[0],[1,7,8,2],[3],[4],[5],[6]]) (.forbid 1 2 3 (.system [[0],[1,7,8,9,2],[3],[4],[5],[6]]) (.forbid 1 2 4 (.system [[0],[1,7,8,9,10,2],[3],[4],[5],[6]]) (.forbid 1 2 5 (.system [[0],[1,7,8,9,10,11,2],[3],[4],[5],[6]]) (.forbid 1 2 6 (.system [[0],[1,7,8,9,10,11,12,2],[3],[4],[5],[6]]) (.forbid 1 3 1 (.system [[0],[1,7,3],[2],[4],[5],[6]]) (.forbid 1 3 2 (.system [[0],[1,7,8,3],[2],[4],[5],[6]]) (.forbid 1 3 3 (.system [[0],[1,7,8,9,3],[2],[4],[5],[6]]) (.forbid 1 3 4 (.system [[0],[1,7,8,9,10,3],[2],[4],[5],[6]]) (.forbid 1 3 5 (.system [[0],[1,7,8,9,10,11,3],[2],[4],[5],[6]]) (.forbid 1 3 6 (.system [[0],[1,7,8,9,10,11,12,3],[2],[4],[5],[6]]) (.forbid 1 4 1 (.system [[0],[1,7,4],[2],[3],[5],[6]]) (.forbid 1 5 1 (.system [[0],[1,7,5],[2],[3],[4],[6]]) (.forbid 2 3 1 (.system [[0],[1],[2,7,3],[4],[5],[6]]) (.forbid 2 3 2 (.system [[0],[1],[2,7,8,3],[4],[5],[6]]) (.forbid 2 3 3 (.system [[0],[1],[2,7,8,9,3],[4],[5],[6]]) (.forbid 2 3 4 (.system [[0],[1],[2,7,8,9,10,3],[4],[5],[6]]) (.forbid 2 3 5 (.system [[0],[1],[2,7,8,9,10,11,3],[4],[5],[6]]) (.forbid 2 3 6 (.system [[0],[1],[2,7,8,9,10,11,12,3],[4],[5],[6]]) (certificate_137_part_0))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates033
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1045_part_1 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[1,12,13,14,4],[2],[3],[5,6,7,8],[11]]) (.forbid 1 4 4 (.system [[0],[1,12,13,14,15,4],[2],[3],[5],[8],[11]]) (.forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4],[2],[3],[5],[8],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4],[2],[3],[5],[8],[11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,6,7,8,9,10,11],[2],[3],[4]]) (.forbid 1 6 1 (.system [[0],[1,12,6,7,8,9,10,11],[2],[3],[4],[5]]) (.forbid 2 3 1 (.system [[0],[1],[2,12,3],[4],[5,6,7,8,9,10,11]]) (.forbid 2 3 2 (.system [[0],[1],[2,12,13,3],[4],[5,6,7,8,9,10,11]]) (.forbid 2 3 3 (.system [[0],[1],[2,12,13,14,3],[4],[5,6,7,8],[11]]) (.forbid 2 3 4 (.system [[0],[1],[2,12,13,14,15,3],[4],[5],[8],[11]]) (.forbid 2 3 5 (.system [[0],[1],[2,12,13,14,15,16,3],[4],[5],[8],[11]]) (.forbid 2 3 6 (.system [[0],[1],[2,12,13,14,15,16,17,3],[4],[5],[8],[11]]) (.forbid 2 4 1 (.system [[0],[1],[2,12,4],[3],[5,6,7,8,9,10,11]]) (.forbid 2 4 2 (.system [[0],[1],[2,12,13,4],[3],[5,6,7,8,9,10,11]]) (.forbid 2 4 3 (.system [[0],[1],[2,12,13,14,4],[3],[5,6,7,8],[11]]) (.forbid 2 4 4 (.system [[0],[1],[2,12,13,14,15,4],[3],[5],[8],[11]]) (.forbid 2 4 5 (.system [[0],[1],[2,12,13,14,15,16,4],[3],[5],[8],[11]]) (.forbid 2 4 6 (.system [[0],[1],[2,12,13,14,15,16,17,4],[3],[5],[8],[11]]) (.forbid 2 5 1 (.system [[0],[1],[2,12,5,6,7,8,9,10,11],[3],[4]]) (.forbid 2 6 1 (.system [[0],[1],[2,12,6,7,8,9,10,11],[3],[4],[5]]) (certificate_1045_part_0))))))))))))))))))))

noncomputable def certificate_1045_part_2 : FiniteCertificate := .forbid 0 4 3 (.system [[0,12,13,14,4],[1],[2],[3],[5,6,7,8],[11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4],[1],[2],[3],[5],[8],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4],[1],[2],[3],[5],[8],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4],[1],[2],[3],[5],[8],[11]]) (.forbid 0 5 1 (.system [[0,12,5,6,7,8,9,10,11],[1],[2],[3],[4]]) (.forbid 0 6 1 (.system [[0,12,6,7,8,9,10,11],[1],[2],[3],[4],[5]]) (.forbid 1 2 1 (.system [[0],[1,12,2],[3],[4],[5,6,7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2],[3],[4],[5,6,7,8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2],[3],[4],[5,6,7,8],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2],[3],[4],[5],[8],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2],[3],[4],[5],[8],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[3],[4],[5],[8],[11]]) (.forbid 1 3 1 (.system [[0],[1,12,3],[2],[4],[5,6,7,8,9,10,11]]) (.forbid 1 3 2 (.system [[0],[1,12,13,3],[2],[4],[5,6,7,8,9,10,11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3],[2],[4],[5,6,7,8],[11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3],[2],[4],[5],[8],[11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3],[2],[4],[5],[8],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3],[2],[4],[5],[8],[11]]) (.forbid 1 4 1 (.system [[0],[1,12,4],[2],[3],[5,6,7,8,9,10,11]]) (.forbid 1 4 2 (.system [[0],[1,12,13,4],[2],[3],[5,6,7,8,9,10,11]]) (certificate_1045_part_1))))))))))))))))))))

noncomputable def certificate_1045 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2],[3],[4],[5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2],[3],[4],[5,6,7,8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[3],[4],[5,6,7,8],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2],[3],[4],[5],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[3],[4],[5],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[3],[4],[5],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2],[1],[3],[4],[5,6,7,8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2],[1],[3],[4],[5,6,7,8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[3],[4],[5,6,7,8],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2],[1],[3],[4],[5],[8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[3],[4],[5],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[3],[4],[5],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3],[1],[2],[4],[5,6,7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3],[1],[2],[4],[5,6,7,8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3],[1],[2],[4],[5,6,7,8],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3],[1],[2],[4],[5],[8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3],[1],[2],[4],[5],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3],[1],[2],[4],[5],[8],[11]]) (.forbid 0 4 1 (.system [[0,12,4],[1],[2],[3],[5,6,7,8,9,10,11]]) (.forbid 0 4 2 (.system [[0,12,13,4],[1],[2],[3],[5,6,7,8,9,10,11]]) (certificate_1045_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates035
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1097_part_1 : FiniteCertificate := .forbid 1 5 2 (.system [[0],[1,12,13,5,6,7],[2,3,4],[9],[11]]) (.forbid 1 5 3 (.system [[0],[1,12,13,14,5],[2,3,4],[7],[9],[11]]) (.forbid 1 5 4 (.system [[0],[1,12,13,14,15,5],[2],[4],[7],[9],[11]]) (.forbid 1 5 5 (.system [[0],[1,12,13,14,15,16,5],[2],[4],[7],[9],[11]]) (.forbid 1 5 6 (.system [[0],[1,12,13,14,15,16,17,5],[2],[4],[7],[9],[11]]) (.forbid 1 6 1 (.system [[0],[1,12,6,5],[2,3,4],[7,8,9],[11]]) (.forbid 2 3 1 (.system [[0],[1],[2,12,3,4],[5,6,7,8,9],[11]]) (.forbid 2 3 2 (.system [[0],[1],[2,12,13,3,4],[5,6,7],[9],[11]]) (.forbid 2 3 3 (.system [[0],[1],[2,12,13,14,3,4],[5],[7],[9],[11]]) (.forbid 2 3 4 (.system [[0],[1],[2,12,13,14,15,3,4],[5],[7],[9],[11]]) (.forbid 2 3 5 (.system [[0],[1],[2,12,13,14,15,16,3,4],[5],[7],[9],[11]]) (.forbid 2 3 6 (.system [[0],[1],[2,12,13,14,15,16,17,3,4],[5],[7],[9],[11]]) (.forbid 2 5 1 (.system [[0],[1],[4,3,2,12,5,6,7,8,9,10,11]]) (.forbid 2 5 2 (.system [[0],[1],[4,3,2,12,13,5,6,7],[9],[11]]) (.forbid 2 5 3 (.system [[0],[1],[4,3,2,12,13,14,5],[7],[9],[11]]) (.forbid 2 5 4 (.system [[0],[1],[2,12,13,14,15,5],[4],[7],[9],[11]]) (.forbid 2 5 5 (.system [[0],[1],[2,12,13,14,15,16,5],[4],[7],[9],[11]]) (.forbid 2 5 6 (.system [[0],[1],[2,12,13,14,15,16,17,5],[4],[7],[9],[11]]) (.forbid 2 6 1 (.system [[0],[1],[4,3,2,12,6,5],[7,8,9],[11]]) (.forbid 2 8 1 (.system [[0],[1],[4,3,2,12,8,7,6,5],[9],[11]]) (certificate_1097_part_0))))))))))))))))))))

noncomputable def certificate_1097_part_2 : FiniteCertificate := .forbid 0 5 2 (.system [[0,12,13,5,6,7],[1],[2,3,4],[9],[11]]) (.forbid 0 5 3 (.system [[0,12,13,14,5],[1],[2,3,4],[7],[9],[11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5],[1],[2],[4],[7],[9],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5],[1],[2],[4],[7],[9],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5],[1],[2],[4],[7],[9],[11]]) (.forbid 0 6 1 (.system [[0,12,6,5],[1],[2,3,4],[7,8,9],[11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3,4],[5,6,7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3,4],[5,6,7],[9],[11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2,3,4],[5],[7],[9],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2],[4],[5],[7],[9],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2],[4],[5],[7],[9],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 1 (.system [[0],[1,12,3,2],[4],[5,6,7,8,9],[11]]) (.forbid 1 3 2 (.system [[0],[1,12,13,3,2],[4],[5,6,7],[9],[11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 4 1 (.system [[0],[1,12,4,3,2],[5,6,7,8,9,10,11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,6,7,8,9,10,11],[2,3,4]]) (certificate_1097_part_1))))))))))))))))))))

noncomputable def certificate_1097 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2,3,4],[5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2,3,4],[5,6,7],[9],[11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2,3,4],[5],[7],[9],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2],[4],[5],[7],[9],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[4],[5],[7],[9],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[4],[5],[7],[9],[11]]) (.forbid 0 2 1 (.system [[0,12,2,3,4],[1],[5,6,7,8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2,3,4],[1],[5,6,7],[9],[11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2,3,4],[1],[5],[7],[9],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2],[1],[4],[5,6,7,8,9],[11]]) (.forbid 0 3 2 (.system [[0,12,13,3,2],[1],[4],[5,6,7],[9],[11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[1],[4],[5],[7],[9],[11]]) (.forbid 0 4 1 (.system [[0,12,4,3,2],[1],[5,6,7,8,9,10,11]]) (.forbid 0 5 1 (.system [[0,12,5,6,7,8,9,10,11],[1],[2,3,4]]) (certificate_1097_part_2))))))))))))))))))))

noncomputable def certificate_1118_part_2 : FiniteCertificate := .forbid 0 5 3 (.system [[0,14,15,16,5,4],[1],[2],[7],[9],[10,11,12,13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5,4,3,2],[1],[7],[9],[10],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,4],[1],[2],[7],[9],[10],[13]]) (.forbid 0 5 6 (.system [[0,14,15,16,17,18,19,5,4],[1],[2],[7],[9],[10],[13]]) (.forbid 0 6 1 (.system [[0,14,6,5,4,3,2],[1],[7],[9],[10,11,12,13]]) (.forbid 0 8 1 (.system [[0,14,8,7,6,5,4],[1],[2],[9],[10,11,12,13]]) (.forbid 0 9 1 (.system [[0,14,9,8,7,6,5,4,3,2],[1],[10,11,12,13]]) (.forbid 0 10 1 (.system [[0,14,10,11,12,13],[1],[2,3,4,5,6,7,8,9]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3,4,5,6,7,8,9],[10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2],[4,5,6,7],[9],[10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2,3,4,5,6,7],[9],[10],[13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2],[4,5,6,7],[9],[10],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2,3,4],[7],[9],[10],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2],[4],[7],[9],[10],[13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,2],[4,5,6,7],[9],[10,11,12,13]]) (.forbid 1 3 2 (.system [[0],[1,14,15,3,2],[4,5,6,7,8,9],[10],[13]]) (.forbid 1 3 3 (.system [[0],[1,14,15,16,3,2],[4,5,6,7],[9],[10],[13]]) (.forbid 1 3 4 (.system [[0],[1,14,15,16,17,3,2],[4,5,6,7],[9],[10],[13]]) (.forbid 1 3 5 (.system [[0],[1,14,15,16,17,18,3,2],[4],[7],[9],[10],[13]]) (.forbid 1 3 6 (.system [[0],[1,14,15,16,17,18,19,3,2],[4],[7],[9],[10],[13]]) (certificate_1118_part_1))))))))))))))))))))

noncomputable def certificate_1118 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2,3,4,5,6,7,8,9],[10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[2],[4,5,6,7],[9],[10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[2,3,4,5,6,7],[9],[10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[2],[4,5,6,7],[9],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[2,3,4],[7],[9],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1],[2],[4],[7],[9],[10],[13]]) (.forbid 0 2 1 (.system [[0,14,2,3,4,5,6,7,8,9],[1],[10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2],[1],[4,5,6,7],[9],[10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2,3,4,5,6,7],[1],[9],[10],[13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2],[1],[4,5,6,7],[9],[10],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2,3,4],[1],[7],[9],[10],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2],[1],[4],[7],[9],[10],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[1],[4,5,6,7],[9],[10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[1],[4,5,6,7,8,9],[10],[13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[1],[4,5,6,7],[9],[10],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[1],[4,5,6,7],[9],[10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[1],[4],[7],[9],[10],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[1],[4],[7],[9],[10],[13]]) (.forbid 0 5 1 (.system [[0,14,5,6,7],[1],[2,3,4],[9],[10,11,12,13]]) (.forbid 0 5 2 (.system [[0,14,15,5,4,3,2],[1],[7],[9],[10,11,12,13]]) (certificate_1118_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates036
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1147_part_1 : FiniteCertificate := .forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[7],[9],[11],[13]]) (.forbid 1 5 1 (.system [[0,1,14,5,4,3],[2],[7,8,9,10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[7,8,9,10,11],[13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5,4,3],[2],[7,8,9],[11],[13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5,4,3],[2],[7],[9],[11],[13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5],[2],[3],[7],[9],[11],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[7],[9],[11],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[7],[9],[11],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5,4,3],[2],[9,10,11,12,13]]) (.forbid 1 8 1 (.system [[0,1,14,8,7,6,5,4,3],[2],[9,10,11],[13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0,1,2,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,5,4,3],[7,8,9,10,11],[13]]) (.forbid 3 4 1 (.system [[0,1,2],[3,14,4,5,6,7,8,9,10,11],[13]]) (.forbid 3 4 2 (.system [[0,1,2],[3,14,15,4,5,6,7,8,9],[11],[13]]) (.forbid 3 4 3 (.system [[0,1,2],[3,14,15,16,4,5,6,7],[9],[11],[13]]) (.forbid 3 4 4 (.system [[0,1,2],[3,14,15,16,17,4,5],[7],[9],[11],[13]]) (.forbid 3 4 5 (.system [[0],[2],[3,14,15,16,17,18,4,5],[7],[9],[11],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[7],[9],[11],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[3,14,6,5],[7,8,9,10,11,12,13]]) (certificate_1147_part_0))))))))))))))))))))

noncomputable def certificate_1147_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5,4,3],[7],[9],[11],[13]]) (.forbid 0 6 4 (.system [[2,1,0,14,15,16,17,6,5],[3],[7],[9],[11],[13]]) (.forbid 0 6 5 (.system [[0,14,15,16,17,18,6,5],[2],[3],[7],[9],[11],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[7],[9],[11],[13]]) (.forbid 0 8 1 (.system [[2,1,0,14,8,7,6,5,4,3],[9,10,11],[13]]) (.forbid 0 10 1 (.system [[2,1,0,14,10,9,8,7,6,5,4,3],[11],[13]]) (.forbid 0 12 1 (.system [[2,1,0,14,12,11],[3,4,5,6,7,8,9],[13]]) (.forbid 0 13 1 (.system [[2,1,0,14,13,12,11,10,9,8,7,6,5,4,3]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5,6,7,8,9,10,11],[13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5,6,7,8,9,10,11],[2],[13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,4,5,6,7,8,9],[2],[11],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,4,5,6,7],[2],[9],[11],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,4,5],[2],[7],[9],[11],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3],[2],[5],[7],[9],[11],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[7],[9],[11],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5,6,7,8,9],[11],[13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5,6,7],[9],[11],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5],[7],[9],[11],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[7],[9],[11],[13]]) (certificate_1147_part_1))))))))))))))))))))

noncomputable def certificate_1147 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5,6,7,8,9,10,11],[13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3,4,5,6,7,8,9],[11],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3,4,5,6,7],[9],[11],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3,4,5],[7],[9],[11],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3],[5],[7],[9],[11],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[7],[9],[11],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[2,1,0,14,15,3,4,5,6,7,8,9],[11],[13]]) (.forbid 0 3 3 (.system [[2,1,0,14,15,16,3,4,5,6,7],[9],[11],[13]]) (.forbid 0 3 4 (.system [[2,1,0,14,15,16,17,3,4,5],[7],[9],[11],[13]]) (.forbid 0 3 5 (.system [[2,1,0,14,15,16,17,18,3],[5],[7],[9],[11],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3],[2],[5],[7],[9],[11],[13]]) (.forbid 0 4 1 (.system [[2,1,0,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 0 4 2 (.system [[2,1,0,14,15,4,3],[5,6,7,8,9],[11],[13]]) (.forbid 0 4 3 (.system [[2,1,0,14,15,16,4,3],[5,6,7],[9],[11],[13]]) (.forbid 0 4 4 (.system [[2,1,0,14,15,16,17,4,3],[5],[7],[9],[11],[13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3],[2],[5],[7],[9],[11],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[7],[9],[11],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,5,4,3],[7,8,9,10,11],[13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5,4,3],[7,8,9],[11],[13]]) (certificate_1147_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates037
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1159_part_1_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_1159_M))))))))))))))))

noncomputable def certificate_1159_part_2_M : ForbiddenMatrix := ((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_1159_part_1_M))))))))))))))))

noncomputable def certificate_1159_part_3_M : ForbiddenMatrix := ((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (certificate_1159_part_2_M))))))))))))))))

noncomputable def certificate_1159_part_4_M : ForbiddenMatrix := ((1,2,1) :: (((0,7,6) :: (((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,6,6) :: (((0,6,5) :: (certificate_1159_part_3_M))))))))))))))))

noncomputable def certificate_1159_part_5_M : ForbiddenMatrix := ((1,4,1) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (certificate_1159_part_4_M))))))))))))))))

noncomputable def certificate_1159_part_6_M : ForbiddenMatrix := ((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((1,5,1) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (certificate_1159_part_5_M))))))))))))))))

noncomputable def certificate_1159_part_7_M : ForbiddenMatrix := ((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,7,2) :: (((1,6,5) :: (certificate_1159_part_6_M))))))))))))))))

noncomputable def certificate_1159_part_8_M : ForbiddenMatrix := ((2,6,2) :: (((2,6,1) :: (((2,5,1) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (((2,3,4) :: (certificate_1159_part_7_M))))))))))))))))

noncomputable def certificate_1159_part_9_M : ForbiddenMatrix := ((3,4,1) :: (((2,7,5) :: (((2,7,4) :: (((2,7,3) :: (((2,7,2) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_1159_part_8_M))))))))))))))))

noncomputable def certificate_1159_part_10_M : ForbiddenMatrix := ((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (((3,6,1) :: (((3,5,1) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (certificate_1159_part_9_M))))))))))))))))

noncomputable def certificate_1159_part_11_M : ForbiddenMatrix := ((4,6,2) :: (((4,6,1) :: (((4,5,1) :: (((3,7,5) :: (((3,7,4) :: (((3,7,3) :: (((3,7,2) :: (((3,6,5) :: (certificate_1159_part_10_M))))))))))))))))

noncomputable def certificate_1159_part_12_M : ForbiddenMatrix := ((5,6,1) :: (((4,7,5) :: (((4,7,4) :: (((4,7,3) :: (((4,7,2) :: (((4,6,5) :: (((4,6,4) :: (((4,6,3) :: (certificate_1159_part_11_M))))))))))))))))

noncomputable def certificate_1159_part_13_M : ForbiddenMatrix := ((0,1,5) :: (((6,7,6) :: (((6,7,5) :: (((6,7,4) :: (((6,7,3) :: (((6,7,2) :: (((6,7,1) :: (certificate_1159_part_12_M))))))))))))))

noncomputable def certificate_1159_part_14_M : ForbiddenMatrix := ((4,7,1) :: (((3,7,1) :: (((2,7,1) :: (((1,7,1) :: (((0,7,1) :: (((0,4,5) :: (((0,3,5) :: (((0,2,5) :: (certificate_1159_part_13_M))))))))))))))))

noncomputable def certificate_1159_part_15_M : ForbiddenMatrix := ((0,8,3) :: (((0,6,0) :: (((6,7,6) :: (((6,7,5) :: (((6,7,4) :: (((6,7,3) :: (((6,7,2) :: (((6,7,1) :: (certificate_1159_part_12_M))))))))))))))))

noncomputable def certificate_1159_part_16_M : ForbiddenMatrix := ((1,8,6) :: (((1,8,5) :: (((1,8,4) :: (((1,8,3) :: (((1,6,6) :: (((0,8,6) :: (((0,8,5) :: (((0,8,4) :: (certificate_1159_part_15_M))))))))))))))))

noncomputable def certificate_1159_part_17_M : ForbiddenMatrix := ((6,8,3) :: (((6,8,2) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (((2,8,5) :: (((2,8,4) :: (((2,8,3) :: (certificate_1159_part_16_M))))))))))))))))

noncomputable def certificate_1159_part_18_M : ForbiddenMatrix := ((0,3,5) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((6,8,6) :: (((6,8,5) :: (((6,8,4) :: (certificate_1159_part_17_M))))))))))))))

noncomputable def certificate_1159_part_19_M : ForbiddenMatrix := ((2,8,2) :: (((2,8,1) :: (((1,8,2) :: (((1,8,1) :: (((1,3,5) :: (((1,2,5) :: (((0,8,2) :: (((0,8,1) :: (certificate_1159_part_18_M))))))))))))))))

noncomputable def certificate_1159_part_20_M : ForbiddenMatrix := ((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((0,5,5) :: (((0,7,0) :: (((6,8,6) :: (((6,8,5) :: (((6,8,4) :: (certificate_1159_part_17_M))))))))))))))))

noncomputable def certificate_1159_part_21_M : ForbiddenMatrix := ((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (((2,5,2) :: (((1,5,5) :: (certificate_1159_part_20_M))))))))))))))))

noncomputable def certificate_1159_part_22_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (certificate_1159_part_21_M))))))))))))))

noncomputable def certificate_1159_part_23_M : ForbiddenMatrix := ((0,7,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (certificate_1159_part_22_M))))))))))))))))

noncomputable def certificate_1159_part_24_M : ForbiddenMatrix := ((1,7,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (certificate_1159_part_23_M))))))))))))))))

noncomputable def certificate_1159_part_25_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (certificate_1159_part_24_M))))))))))))))))

noncomputable def certificate_1159_part_26_M : ForbiddenMatrix := ((0,1,5) :: (((0,8,0) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (certificate_1159_part_21_M))))))))))))))

noncomputable def certificate_1159_part_27_M : ForbiddenMatrix := ((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_1159_part_26_M))))))))))))))))

noncomputable def certificate_1159_part_28_M : ForbiddenMatrix := ((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (certificate_1159_part_27_M))))))))))))))))

noncomputable def certificate_1159_part_29_M : ForbiddenMatrix := ((3,4,5) :: (((2,8,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,8,1) :: (certificate_1159_part_28_M))))))))))))))))

noncomputable def certificate_1159_part_30_M : ForbiddenMatrix := ((0,9,0) :: (((0,8,0) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (certificate_1159_part_21_M))))))))))))))

noncomputable def certificate_1159_part_31_M : ForbiddenMatrix := ((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_1159_part_30_M))))))))))))))))

noncomputable def certificate_1159_part_32_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,9,1) :: (((0,5,6) :: (certificate_1159_part_31_M))))))))))))))))

noncomputable def certificate_1159_part_33_M : ForbiddenMatrix := ((2,9,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,9,1) :: (((1,5,6) :: (certificate_1159_part_32_M))))))))))))))))

noncomputable def certificate_1159_part_34_M : ForbiddenMatrix := ((0,10,0) :: (((0,9,0) :: (((0,8,0) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (certificate_1159_part_21_M))))))))))))))))

noncomputable def certificate_1159_part_35_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_1159_part_34_M))))))))))))))

noncomputable def certificate_1159_part_36_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,10,1) :: (((0,5,6) :: (((0,4,6) :: (certificate_1159_part_35_M))))))))))))))))

noncomputable def certificate_1159_part_37_M : ForbiddenMatrix := ((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,10,1) :: (((1,5,6) :: (((1,4,6) :: (certificate_1159_part_36_M))))))))))))))))

noncomputable def certificate_1159_part_38_M : ForbiddenMatrix := ((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((0,11,0) :: (certificate_1159_part_34_M))))))))))))))))

noncomputable def certificate_1159_part_39_M : ForbiddenMatrix := ((4,7,1) :: (((3,7,1) :: (((2,7,1) :: (((1,7,1) :: (((0,7,1) :: (((0,1,5) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_40_M : ForbiddenMatrix := ((0,8,1) :: (((0,3,5) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_41_M : ForbiddenMatrix := ((3,8,1) :: (((2,8,2) :: (((2,8,1) :: (((1,8,2) :: (((1,8,1) :: (((1,3,5) :: (((1,2,5) :: (((0,8,2) :: (certificate_1159_part_40_M))))))))))))))))

noncomputable def certificate_1159_part_42_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((1,7,0) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_43_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (certificate_1159_part_42_M))))))))))))))))

noncomputable def certificate_1159_part_44_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((1,7,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (certificate_1159_part_43_M))))))))))))))))

noncomputable def certificate_1159_part_45_M : ForbiddenMatrix := ((3,7,1) :: (((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (certificate_1159_part_44_M))))))))))))))))

noncomputable def certificate_1159_part_46_M : ForbiddenMatrix := ((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_47_M : ForbiddenMatrix := ((1,2,5) :: (((0,8,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (certificate_1159_part_46_M))))))))))))))))

noncomputable def certificate_1159_part_48_M : ForbiddenMatrix := ((2,3,5) :: (((1,8,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (certificate_1159_part_47_M))))))))))))))))

noncomputable def certificate_1159_part_49_M : ForbiddenMatrix := ((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,8,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (certificate_1159_part_48_M))))))))))))))))

noncomputable def certificate_1159_part_50_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_51_M : ForbiddenMatrix := ((0,9,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (certificate_1159_part_50_M))))))))))))))))

noncomputable def certificate_1159_part_52_M : ForbiddenMatrix := ((1,9,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (certificate_1159_part_51_M))))))))))))))))

noncomputable def certificate_1159_part_53_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,9,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (certificate_1159_part_52_M))))))))))))))))

noncomputable def certificate_1159_part_54_M : ForbiddenMatrix := ((0,1,5) :: (((1,10,0) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_55_M : ForbiddenMatrix := ((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_1159_part_54_M))))))))))))))))

noncomputable def certificate_1159_part_56_M : ForbiddenMatrix := ((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,10,1) :: (certificate_1159_part_55_M))))))))))))))))

noncomputable def certificate_1159_part_57_M : ForbiddenMatrix := ((3,4,5) :: (((2,10,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,10,1) :: (certificate_1159_part_56_M))))))))))))))))

noncomputable def certificate_1159_part_58_M : ForbiddenMatrix := ((1,11,0) :: (((1,10,0) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))

noncomputable def certificate_1159_part_59_M : ForbiddenMatrix := ((2,6,0) :: (((1,11,0) :: (((1,10,0) :: (((1,9,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((5,7,5) :: (certificate_1159_part_38_M))))))))))))))))

noncomputable def certificate_1159_part_60_M : ForbiddenMatrix := ((0,8,1) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,5) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))

noncomputable def certificate_1159_part_61_M : ForbiddenMatrix := ((3,8,1) :: (((2,8,2) :: (((2,8,1) :: (((2,3,5) :: (((1,8,2) :: (((1,8,1) :: (((1,2,5) :: (((0,8,2) :: (certificate_1159_part_60_M))))))))))))))))

noncomputable def certificate_1159_part_62_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((2,7,0) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))

noncomputable def certificate_1159_part_63_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (certificate_1159_part_62_M))))))))))))))))

noncomputable def certificate_1159_part_64_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((1,7,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (certificate_1159_part_63_M))))))))))))))))

noncomputable def certificate_1159_part_65_M : ForbiddenMatrix := ((3,7,1) :: (((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (certificate_1159_part_64_M))))))))))))))))

noncomputable def certificate_1159_part_66_M : ForbiddenMatrix := ((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((2,8,0) :: (((2,7,0) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))

noncomputable def certificate_1159_part_67_M : ForbiddenMatrix := ((1,2,5) :: (((0,8,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (certificate_1159_part_66_M))))))))))))))))

noncomputable def certificate_1159_part_68_M : ForbiddenMatrix := ((2,3,5) :: (((1,8,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (certificate_1159_part_67_M))))))))))))))))

noncomputable def certificate_1159_part_69_M : ForbiddenMatrix := ((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,8,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (certificate_1159_part_68_M))))))))))))))))

noncomputable def certificate_1159_part_70_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))

noncomputable def certificate_1159_part_71_M : ForbiddenMatrix := ((0,9,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (certificate_1159_part_70_M))))))))))))))))

noncomputable def certificate_1159_part_72_M : ForbiddenMatrix := ((1,9,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (certificate_1159_part_71_M))))))))))))))))

noncomputable def certificate_1159_part_73_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,9,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (certificate_1159_part_72_M))))))))))))))))

noncomputable def certificate_1159_part_74_M : ForbiddenMatrix := ((0,1,5) :: (((2,10,0) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))

noncomputable def certificate_1159_part_75_M : ForbiddenMatrix := ((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_1159_part_74_M))))))))))))))))

noncomputable def certificate_1159_part_76_M : ForbiddenMatrix := ((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,10,1) :: (certificate_1159_part_75_M))))))))))))))))

noncomputable def certificate_1159_part_77_M : ForbiddenMatrix := ((3,4,5) :: (((2,10,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,10,1) :: (certificate_1159_part_76_M))))))))))))))))

noncomputable def certificate_1159_part_78_M : ForbiddenMatrix := ((2,11,0) :: (((2,10,0) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))

noncomputable def certificate_1159_part_79_M : ForbiddenMatrix := ((3,6,0) :: (((2,11,0) :: (((2,10,0) :: (((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,8,6) :: (((2,6,6) :: (certificate_1159_part_59_M))))))))))))))))

noncomputable def certificate_1159_part_80_M : ForbiddenMatrix := ((0,8,1) :: (((0,3,6) :: (((0,3,5) :: (((0,2,5) :: (((0,1,5) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))

noncomputable def certificate_1159_part_81_M : ForbiddenMatrix := ((3,8,1) :: (((2,8,2) :: (((2,8,1) :: (((2,3,5) :: (((1,8,2) :: (((1,8,1) :: (((1,3,5) :: (((0,8,2) :: (certificate_1159_part_80_M))))))))))))))))

noncomputable def certificate_1159_part_82_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((3,7,0) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))

noncomputable def certificate_1159_part_83_M : ForbiddenMatrix := ((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (certificate_1159_part_82_M))))))))))))))))

noncomputable def certificate_1159_part_84_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((1,7,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (certificate_1159_part_83_M))))))))))))))))

noncomputable def certificate_1159_part_85_M : ForbiddenMatrix := ((3,7,1) :: (((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,7,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (certificate_1159_part_84_M))))))))))))))))

noncomputable def certificate_1159_part_86_M : ForbiddenMatrix := ((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((3,8,0) :: (((3,7,0) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))

noncomputable def certificate_1159_part_87_M : ForbiddenMatrix := ((1,2,5) :: (((0,8,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (certificate_1159_part_86_M))))))))))))))))

noncomputable def certificate_1159_part_88_M : ForbiddenMatrix := ((2,3,5) :: (((1,8,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (certificate_1159_part_87_M))))))))))))))))

noncomputable def certificate_1159_part_89_M : ForbiddenMatrix := ((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,8,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (certificate_1159_part_88_M))))))))))))))))

noncomputable def certificate_1159_part_90_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((3,9,0) :: (((3,8,0) :: (((3,7,0) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))

noncomputable def certificate_1159_part_91_M : ForbiddenMatrix := ((0,9,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (certificate_1159_part_90_M))))))))))))))))

noncomputable def certificate_1159_part_92_M : ForbiddenMatrix := ((1,9,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (certificate_1159_part_91_M))))))))))))))))

noncomputable def certificate_1159_part_93_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((2,9,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (certificate_1159_part_92_M))))))))))))))))

noncomputable def certificate_1159_part_94_M : ForbiddenMatrix := ((0,1,5) :: (((3,10,0) :: (((3,9,0) :: (((3,8,0) :: (((3,7,0) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))

noncomputable def certificate_1159_part_95_M : ForbiddenMatrix := ((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_1159_part_94_M))))))))))))))))

noncomputable def certificate_1159_part_96_M : ForbiddenMatrix := ((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,10,1) :: (certificate_1159_part_95_M))))))))))))))))

noncomputable def certificate_1159_part_97_M : ForbiddenMatrix := ((3,4,5) :: (((2,10,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,10,1) :: (certificate_1159_part_96_M))))))))))))))))

noncomputable def certificate_1159_part_98_M : ForbiddenMatrix := ((3,11,0) :: (((3,10,0) :: (((3,9,0) :: (((3,8,0) :: (((3,7,0) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))

noncomputable def certificate_1159_part_99_M : ForbiddenMatrix := ((4,6,0) :: (((3,11,0) :: (((3,10,0) :: (((3,9,0) :: (((3,8,0) :: (((3,7,0) :: (((3,8,6) :: (((3,6,6) :: (certificate_1159_part_79_M))))))))))))))))

noncomputable def certificate_1159_part_100_M : ForbiddenMatrix := ((0,2,5) :: (((0,1,5) :: (((4,8,6) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,6,6) :: (certificate_1159_part_99_M))))))))))))))

noncomputable def certificate_1159_part_101_E : List (ℕ × ℕ) := certificate_1159_part_100_E

noncomputable def certificate_1159_part_101_M : ForbiddenMatrix := ((2,4,5) :: (((1,8,2) :: (((1,8,1) :: (((1,4,5) :: (((0,8,2) :: (((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (certificate_1159_part_100_M))))))))))))))))

noncomputable def certificate_1159_part_102_M : ForbiddenMatrix := ((0,1,5) :: (((4,7,0) :: (((4,8,6) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,6,6) :: (certificate_1159_part_99_M))))))))))))))

noncomputable def certificate_1159_part_103_M : ForbiddenMatrix := ((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_1159_part_102_M))))))))))))))))

noncomputable def certificate_1159_part_104_M : ForbiddenMatrix := ((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (certificate_1159_part_103_M))))))))))))))))

noncomputable def certificate_1159_part_105_M : ForbiddenMatrix := ((3,4,5) :: (((2,7,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,7,1) :: (certificate_1159_part_104_M))))))))))))))))

noncomputable def certificate_1159_part_106_M : ForbiddenMatrix := ((4,8,0) :: (((4,7,0) :: (((4,8,6) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,6,6) :: (certificate_1159_part_99_M))))))))))))))

noncomputable def certificate_1159_part_107_M : ForbiddenMatrix := ((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_1159_part_106_M))))))))))))))))

noncomputable def certificate_1159_part_108_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,5,6) :: (certificate_1159_part_107_M))))))))))))))))

noncomputable def certificate_1159_part_109_M : ForbiddenMatrix := ((2,8,1) :: (((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,8,1) :: (((1,5,6) :: (certificate_1159_part_108_M))))))))))))))))

noncomputable def certificate_1159_part_110_M : ForbiddenMatrix := ((4,9,0) :: (((4,8,0) :: (((4,7,0) :: (((4,8,6) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,6,6) :: (certificate_1159_part_99_M))))))))))))))))

noncomputable def certificate_1159_part_111_M : ForbiddenMatrix := ((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (certificate_1159_part_110_M))))))))))))))

noncomputable def certificate_1159_part_112_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,9,1) :: (((0,5,6) :: (((0,4,6) :: (certificate_1159_part_111_M))))))))))))))))

noncomputable def certificate_1159_part_113_M : ForbiddenMatrix := ((2,5,6) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,9,1) :: (((1,5,6) :: (((1,4,6) :: (certificate_1159_part_112_M))))))))))))))))

noncomputable def certificate_1159_part_114_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((4,10,0) :: (certificate_1159_part_110_M))))))))))))))

noncomputable def certificate_1159_part_115_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,10,1) :: (((0,5,6) :: (((0,4,6) :: (((0,4,5) :: (certificate_1159_part_114_M))))))))))))))))

noncomputable def certificate_1159_part_116_M : ForbiddenMatrix := ((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,10,1) :: (((1,5,6) :: (((1,4,6) :: (((1,4,5) :: (certificate_1159_part_115_M))))))))))))))))

noncomputable def certificate_1159_part_117_M : ForbiddenMatrix := ((4,10,1) :: (((4,5,6) :: (((3,10,1) :: (((3,5,6) :: (((3,4,6) :: (((3,4,5) :: (((2,10,1) :: (((2,5,6) :: (certificate_1159_part_116_M))))))))))))))))

noncomputable def certificate_1159_part_118_M : ForbiddenMatrix := ((5,6,6) :: (((4,13,1) :: (((3,13,1) :: (((2,13,1) :: (((1,13,1) :: (((0,13,1) :: (((4,11,0) :: (((4,10,0) :: (certificate_1159_part_110_M))))))))))))))))

noncomputable def certificate_1159_part_119_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((5,7,0) :: (certificate_1159_part_118_M))))))))))))))

noncomputable def certificate_1159_part_120_M : ForbiddenMatrix := ((1,4,5) :: (((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,7,1) :: (((0,4,6) :: (((0,4,5) :: (certificate_1159_part_119_M))))))))))))))))

noncomputable def certificate_1159_part_121_M : ForbiddenMatrix := ((3,4,5) :: (((2,7,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,7,1) :: (((1,4,6) :: (certificate_1159_part_120_M))))))))))))))))

noncomputable def certificate_1159_part_122_M : ForbiddenMatrix := ((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((5,8,0) :: (((5,7,0) :: (certificate_1159_part_118_M))))))))))))))

noncomputable def certificate_1159_part_123_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,8,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (certificate_1159_part_122_M))))))))))))))))

noncomputable def certificate_1159_part_124_M : ForbiddenMatrix := ((2,8,1) :: (((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,8,1) :: (((1,4,6) :: (((1,4,5) :: (certificate_1159_part_123_M))))))))))))))))

noncomputable def certificate_1159_part_125_M : ForbiddenMatrix := ((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((5,9,0) :: (((5,8,0) :: (((5,7,0) :: (certificate_1159_part_118_M))))))))))))))

noncomputable def certificate_1159_part_126_M : ForbiddenMatrix := ((1,3,5) :: (((1,2,6) :: (((1,2,5) :: (((0,9,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (certificate_1159_part_125_M))))))))))))))))

noncomputable def certificate_1159_part_127_M : ForbiddenMatrix := ((2,4,6) :: (((2,4,5) :: (((2,3,6) :: (((2,3,5) :: (((1,9,1) :: (((1,4,6) :: (((1,4,5) :: (((1,3,6) :: (certificate_1159_part_126_M))))))))))))))))

noncomputable def certificate_1159_part_128_M : ForbiddenMatrix := ((0,13,5) :: (((0,13,4) :: (((0,13,3) :: (((0,13,2) :: (((5,10,0) :: (((5,9,0) :: (((5,8,0) :: (((5,7,0) :: (certificate_1159_part_118_M))))))))))))))))

noncomputable def certificate_1159_part_129_M : ForbiddenMatrix := ((2,13,5) :: (((2,13,4) :: (((2,13,3) :: (((2,13,2) :: (((1,13,5) :: (((1,13,4) :: (((1,13,3) :: (((1,13,2) :: (certificate_1159_part_128_M))))))))))))))))

noncomputable def certificate_1159_part_130_M : ForbiddenMatrix := ((4,13,5) :: (((4,13,4) :: (((4,13,3) :: (((4,13,2) :: (((3,13,5) :: (((3,13,4) :: (((3,13,3) :: (((3,13,2) :: (certificate_1159_part_129_M))))))))))))))))

noncomputable def certificate_1159_part_131_M : ForbiddenMatrix := ((1,14,1) :: (((0,14,5) :: (((0,14,4) :: (((0,14,3) :: (((0,14,2) :: (((0,14,1) :: (((5,12,0) :: (((12,13,1) :: (certificate_1159_part_130_M))))))))))))))))

noncomputable def certificate_1159_part_132_M : ForbiddenMatrix := ((2,14,4) :: (((2,14,3) :: (((2,14,2) :: (((2,14,1) :: (((1,14,5) :: (((1,14,4) :: (((1,14,3) :: (((1,14,2) :: (certificate_1159_part_131_M))))))))))))))))

noncomputable def certificate_1159_part_133_M : ForbiddenMatrix := ((4,14,2) :: (((4,14,1) :: (((3,14,5) :: (((3,14,4) :: (((3,14,3) :: (((3,14,2) :: (((3,14,1) :: (((2,14,5) :: (certificate_1159_part_132_M))))))))))))))))

noncomputable def certificate_1159_part_134_M : ForbiddenMatrix := ((6,14,3) :: (((6,14,2) :: (((6,14,1) :: (((13,14,1) :: (((4,14,5) :: (((4,14,4) :: (((4,14,3) :: (certificate_1159_part_133_M))))))))))))))

noncomputable def certificate_1161 : FiniteCertificate := .forbid 0 1 1 (.system [[0,10,1],[2],[3],[4,5,6,7,8,9]]) (.forbid 0 1 2 (.system [[0,10,11,1],[2],[3],[4],[6,7,8,9]]) (.forbid 0 1 3 (.system [[0,10,11,12,1],[2],[3],[4],[6],[9]]) (.forbid 0 1 4 (.system [[0,10,11,12,13,1],[2],[3],[4],[6],[9]]) (.forbid 0 1 5 (.system [[0,10,11,12,13,14,1],[2],[3],[4],[6],[9]]) (.forbid 0 1 6 (.system [[0,10,11,12,13,14,15,1],[2],[3],[4],[6],[9]]) (.forbid 0 2 1 (.system [[0,10,2],[1],[3],[4,5,6,7,8,9]]) (.forbid 0 2 2 (.system [[0,10,11,2],[1],[3],[4],[6,7,8,9]]) (.forbid 0 2 3 (.system [[0,10,11,12,2],[1],[3],[4],[6],[9]]) (.forbid 0 2 4 (.system [[0,10,11,12,13,2],[1],[3],[4],[6],[9]]) (.forbid 0 2 5 (.system [[0,10,11,12,13,14,2],[1],[3],[4],[6],[9]]) (.forbid 0 2 6 (.system [[0,10,11,12,13,14,15,2],[1],[3],[4],[6],[9]]) (.forbid 0 3 1 (.system [[0,10,3],[1],[2],[4,5,6,7,8,9]]) (.forbid 0 3 2 (.system [[0,10,11,3],[1],[2],[4],[6,7,8,9]]) (.forbid 0 3 3 (.system [[0,10,11,12,3],[1],[2],[4],[6],[9]]) (.forbid 0 3 4 (.system [[0,10,11,12,13,3],[1],[2],[4],[6],[9]]) (.forbid 0 3 5 (.system [[0,10,11,12,13,14,3],[1],[2],[4],[6],[9]]) (.forbid 0 3 6 (.system [[0,10,11,12,13,14,15,3],[1],[2],[4],[6],[9]]) (.forbid 0 4 1 (.system [[0,10,4,5,6,7,8,9],[1],[2],[3]]) (.forbid 0 4 2 (.system [[0,10,11,4],[1],[2],[3],[6,7,8,9]]) (certificate_1161_part_3))))))))))))))))))))

noncomputable def certificate_1175_part_1_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,1) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_1175_M))))))))))))))))

noncomputable def certificate_1175_part_2_M : ForbiddenMatrix := ((0,3,2) :: (((0,3,1) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (((0,1,5) :: (((0,4,4) :: (((0,4,3) :: (certificate_1175_part_1_M))))))))))))))))

noncomputable def certificate_1175_part_3_M : ForbiddenMatrix := ((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((0,4,6) :: (((0,4,5) :: (((0,3,6) :: (((0,3,5) :: (((0,3,3) :: (certificate_1175_part_2_M))))))))))))))))

noncomputable def certificate_1175_part_4_M : ForbiddenMatrix := ((1,2,5) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,8,1) :: (((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (certificate_1175_part_3_M))))))))))))))))

noncomputable def certificate_1175_part_5_M : ForbiddenMatrix := ((1,4,2) :: (((1,4,1) :: (((1,3,6) :: (((1,3,5) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,6) :: (certificate_1175_part_4_M))))))))))))))))

noncomputable def certificate_1175_part_6_M : ForbiddenMatrix := ((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (certificate_1175_part_5_M))))))))))))))))

noncomputable def certificate_1175_part_7_M : ForbiddenMatrix := ((2,3,6) :: (((2,3,5) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,8,1) :: (((1,5,6) :: (((1,5,5) :: (certificate_1175_part_6_M))))))))))))))))

noncomputable def certificate_1175_part_8_M : ForbiddenMatrix := ((2,5,2) :: (((2,5,1) :: (((2,4,6) :: (((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (certificate_1175_part_7_M))))))))))))))))

noncomputable def certificate_1175_part_9_M : ForbiddenMatrix := ((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (((2,8,1) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (certificate_1175_part_8_M))))))))))))))))

noncomputable def certificate_1175_part_10_M : ForbiddenMatrix := ((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (((3,5,1) :: (((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (certificate_1175_part_9_M))))))))))))))))

noncomputable def certificate_1175_part_11_M : ForbiddenMatrix := ((4,5,6) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,8,1) :: (((3,5,6) :: (certificate_1175_part_10_M))))))))))))))))

noncomputable def certificate_1175_part_12_M : ForbiddenMatrix := ((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((5,10,1) :: (((5,6,1) :: (certificate_1175_part_11_M))))))))))))))

noncomputable def certificate_1175_part_13_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((4,10,1) :: (((0,5,0) :: (((5,10,1) :: (((5,6,1) :: (certificate_1175_part_11_M))))))))))))))

noncomputable def certificate_1175_part_14_M : ForbiddenMatrix := ((4,7,1) :: (((3,7,1) :: (((2,7,1) :: (((2,3,4) :: (((1,7,1) :: (((1,3,4) :: (((1,2,4) :: (((0,7,1) :: (certificate_1175_part_13_M))))))))))))))))

noncomputable def certificate_1175_part_15_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,4) :: (((0,6,0) :: (((4,10,1) :: (((0,5,0) :: (((5,10,1) :: (((5,6,1) :: (certificate_1175_part_11_M))))))))))))))

noncomputable def certificate_1175_part_16_M : ForbiddenMatrix := ((3,6,1) :: (((2,6,1) :: (((2,3,4) :: (((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (certificate_1175_part_15_M))))))))))))))))

noncomputable def certificate_1175_part_17_M : ForbiddenMatrix := ((0,1,4) :: (((0,7,0) :: (((0,6,0) :: (((4,10,1) :: (((0,5,0) :: (((5,10,1) :: (((5,6,1) :: (certificate_1175_part_11_M))))))))))))))

noncomputable def certificate_1175_part_18_M : ForbiddenMatrix := ((2,7,1) :: (((2,3,4) :: (((1,7,1) :: (((1,3,4) :: (((1,2,4) :: (((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (certificate_1175_part_17_M))))))))))))))))

noncomputable def certificate_1175_part_19_M : ForbiddenMatrix := ((0,8,0) :: (((0,7,0) :: (((0,6,0) :: (((4,10,1) :: (((0,5,0) :: (((5,10,1) :: (((5,6,1) :: (certificate_1175_part_11_M))))))))))))))

noncomputable def certificate_1175_part_20_M : ForbiddenMatrix := ((2,3,4) :: (((1,9,1) :: (((1,3,4) :: (((1,2,4) :: (((0,9,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (certificate_1175_part_19_M))))))))))))))))

noncomputable def certificate_1175_part_21_M : ForbiddenMatrix := ((0,10,0) :: (((0,8,0) :: (((0,7,0) :: (((0,6,0) :: (((4,10,1) :: (((0,5,0) :: (((5,10,1) :: (((5,6,1) :: (certificate_1175_part_11_M))))))))))))))))

noncomputable def certificate_1175_part_22_M : ForbiddenMatrix := ((3,10,1) :: (((2,10,1) :: (((1,10,1) :: (((0,10,4) :: (((0,10,3) :: (((0,10,2) :: (((0,10,1) :: (certificate_1175_part_21_M))))))))))))))

noncomputable def certificate_1175_part_23_M : ForbiddenMatrix := ((0,11,0) :: (((3,10,1) :: (((2,10,1) :: (((1,10,1) :: (((0,10,4) :: (((0,10,3) :: (((0,10,2) :: (((0,10,1) :: (certificate_1175_part_21_M))))))))))))))))

noncomputable def certificate_1175_part_24_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (certificate_1175_part_23_M))))))))))))))

noncomputable def certificate_1175_part_25_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((1,5,0) :: (certificate_1175_part_23_M))))))))))))))

noncomputable def certificate_1175_part_26_M : ForbiddenMatrix := ((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((1,6,0) :: (((1,5,0) :: (certificate_1175_part_23_M))))))))))))))

noncomputable def certificate_1175_part_27_M : ForbiddenMatrix := ((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((1,7,0) :: (((1,6,0) :: (((1,5,0) :: (certificate_1175_part_23_M))))))))))))))

noncomputable def certificate_1175_part_28_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((1,5,0) :: (certificate_1175_part_23_M))))))))))))))

noncomputable def certificate_1175_part_29_M : ForbiddenMatrix := ((1,10,3) :: (((1,10,2) :: (((1,10,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((1,5,0) :: (certificate_1175_part_23_M))))))))))))))

noncomputable def certificate_1175_part_30_M : ForbiddenMatrix := ((1,11,0) :: (((1,10,3) :: (((1,10,2) :: (((1,10,0) :: (((1,8,0) :: (((1,7,0) :: (((1,6,0) :: (((1,5,0) :: (certificate_1175_part_23_M))))))))))))))))

noncomputable def certificate_1175_part_31_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (certificate_1175_part_30_M))))))))))))))

noncomputable def certificate_1175_part_32_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((2,5,0) :: (certificate_1175_part_30_M))))))))))))))

noncomputable def certificate_1175_part_33_M : ForbiddenMatrix := ((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((2,6,0) :: (((2,5,0) :: (certificate_1175_part_30_M))))))))))))))

noncomputable def certificate_1175_part_34_M : ForbiddenMatrix := ((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((2,7,0) :: (((2,6,0) :: (((2,5,0) :: (certificate_1175_part_30_M))))))))))))))

noncomputable def certificate_1175_part_35_M : ForbiddenMatrix := ((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((2,8,0) :: (((2,7,0) :: (((2,6,0) :: (((2,5,0) :: (certificate_1175_part_30_M))))))))))))))

noncomputable def certificate_1175_part_36_M : ForbiddenMatrix := ((2,10,3) :: (((2,10,2) :: (((2,10,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,0) :: (((2,5,0) :: (certificate_1175_part_30_M))))))))))))))

noncomputable def certificate_1175_part_37_M : ForbiddenMatrix := ((2,11,0) :: (((2,10,3) :: (((2,10,2) :: (((2,10,0) :: (((2,8,0) :: (((2,7,0) :: (((2,6,0) :: (((2,5,0) :: (certificate_1175_part_30_M))))))))))))))))

noncomputable def certificate_1175_part_38_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (certificate_1175_part_37_M))))))))))))))

noncomputable def certificate_1175_part_39_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((0,9,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((3,5,0) :: (certificate_1175_part_37_M))))))))))))))

noncomputable def certificate_1175_part_40_M : ForbiddenMatrix := ((2,10,4) :: (((1,10,6) :: (((1,10,5) :: (((1,10,4) :: (((0,10,6) :: (((0,10,5) :: (((3,10,0) :: (((3,5,0) :: (certificate_1175_part_37_M))))))))))))))))

noncomputable def certificate_1175_part_41_M : ForbiddenMatrix := ((5,10,2) :: (((3,10,6) :: (((3,10,5) :: (((3,10,4) :: (((3,10,3) :: (((3,10,2) :: (((2,10,6) :: (((2,10,5) :: (certificate_1175_part_40_M))))))))))))))))

noncomputable def certificate_1175_part_42_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,4) :: (((6,10,1) :: (((5,10,6) :: (((5,10,5) :: (((5,10,4) :: (((5,10,3) :: (certificate_1175_part_41_M))))))))))))))

noncomputable def certificate_1175_part_43_M : ForbiddenMatrix := ((0,6,3) :: (((0,6,2) :: (((4,6,0) :: (((6,10,1) :: (((5,10,6) :: (((5,10,5) :: (((5,10,4) :: (((5,10,3) :: (certificate_1175_part_41_M))))))))))))))))

noncomputable def certificate_1175_part_44_M : ForbiddenMatrix := ((1,6,6) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((0,6,6) :: (((0,6,5) :: (((0,6,4) :: (certificate_1175_part_43_M))))))))))))))))

noncomputable def certificate_1175_part_45_M : ForbiddenMatrix := ((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (((2,6,6) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (((2,6,2) :: (certificate_1175_part_44_M))))))))))))))))

noncomputable def certificate_1175_part_46_M : ForbiddenMatrix := ((6,7,1) :: (((5,6,6) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((3,6,6) :: (((3,6,5) :: (certificate_1175_part_45_M))))))))))))))))

noncomputable def certificate_1175_part_47_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (certificate_1175_part_46_M))))))))))))))

noncomputable def certificate_1175_part_48_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((4,7,0) :: (certificate_1175_part_46_M))))))))))))))

noncomputable def certificate_1175_part_49_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,4) :: (((4,10,4) :: (((4,10,3) :: (((4,10,2) :: (((4,8,0) :: (((4,7,0) :: (certificate_1175_part_46_M))))))))))))))

noncomputable def certificate_1175_part_50_M : ForbiddenMatrix := ((0,1,4) :: (((4,11,0) :: (((4,10,4) :: (((4,10,3) :: (((4,10,2) :: (((4,8,0) :: (((4,7,0) :: (certificate_1175_part_46_M))))))))))))))

noncomputable def certificate_1175_part_51_M : ForbiddenMatrix := ((4,12,0) :: (((4,11,0) :: (((4,10,4) :: (((4,10,3) :: (((4,10,2) :: (((4,8,0) :: (((4,7,0) :: (certificate_1175_part_46_M))))))))))))))

noncomputable def certificate_1175_part_52_M : ForbiddenMatrix := ((4,13,0) :: (((4,12,0) :: (((4,11,0) :: (((4,10,4) :: (((4,10,3) :: (((4,10,2) :: (((4,8,0) :: (((4,7,0) :: (certificate_1175_part_46_M))))))))))))))))

noncomputable def certificate_1175_part_53_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (certificate_1175_part_52_M))))))))))))))

noncomputable def certificate_1175_part_54_M : ForbiddenMatrix := ((1,2,4) :: (((0,7,1) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((5,7,0) :: (certificate_1175_part_52_M))))))))))))))

noncomputable def certificate_1175_part_55_M : ForbiddenMatrix := ((3,7,1) :: (((3,6,1) :: (((2,7,1) :: (((2,6,1) :: (((2,3,4) :: (((1,7,1) :: (((1,6,1) :: (((1,3,4) :: (certificate_1175_part_54_M))))))))))))))))

noncomputable def certificate_1175_part_56_M : ForbiddenMatrix := ((1,2,4) :: (((0,6,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((5,8,0) :: (((5,7,0) :: (certificate_1175_part_52_M))))))))))))))

noncomputable def certificate_1175_part_57_M : ForbiddenMatrix := ((0,7,1) :: (((0,3,4) :: (((0,2,4) :: (((0,1,4) :: (((5,10,0) :: (((5,8,0) :: (((5,7,0) :: (certificate_1175_part_52_M))))))))))))))

noncomputable def certificate_1181_part_1 : FiniteCertificate := .forbid 2 3 5 (.system [[0],[1],[2,14,15,16,17,18,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 3 6 (.system [[0],[1],[2,14,15,16,17,18,19,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[1],[2,14,4,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 2 (.system [[0],[1],[2,14,15,4,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 3 (.system [[0],[1],[2,14,15,16,4,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 4 (.system [[0],[1],[2,14,15,16,17,4,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 5 (.system [[0],[1],[2,14,15,16,17,18,4,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 6 (.system [[0],[1],[2,14,15,16,17,18,19,4,3],[5],[6],[13]]) (.forbid 2 5 1 (.system [[0],[1],[2,14,5,4,3],[6,7,8,9,10,11,12,13]]) (.forbid 2 6 1 (.system [[0],[1],[2,14,6,7,8,9,10,11,12,13],[3,4,5]]) (.forbid 2 6 2 (.system [[0],[1],[2,14,15,6,7,8,9,10,11,12,13],[3],[5]]) (.forbid 2 6 3 (.system [[0],[1],[2,14,15,16,6,7,8,9,10,11,12,13],[3],[5]]) (.forbid 2 6 4 (.system [[0],[1],[2,14,15,16,17,6,7,8,9,10,11,12,13],[3],[5]]) (.forbid 2 6 5 (.system [[0],[1],[2,14,15,16,17,18,6,7,8,9,10,11,12,13],[3],[5]]) (.forbid 2 6 6 (.system [[0],[1],[2,14,15,16,17,18,19,6,7,8,9,10,11,12,13],[3],[5]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,14,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,14,15,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 3 4 3 (.system [[0],[1],[2],[3,14,15,16,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 3 4 4 (.system [[0],[1],[2],[3,14,15,16,17,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 3 4 5 (.system [[0],[1],[2],[3,14,15,16,17,18,4,5],[6,7,8,9,10,11,12,13]]) (certificate_1181_part_0))))))))))))))))))))

noncomputable def certificate_1181_part_2 : FiniteCertificate := .forbid 1 3 4 (.system [[0],[1,14,15,16,17,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 3 5 (.system [[0],[1,14,15,16,17,18,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 3 6 (.system [[0],[1,14,15,16,17,18,19,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 1 (.system [[0],[1,14,4,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0],[1,14,15,16,4,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 4 (.system [[0],[1,14,15,16,17,4,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 5 (.system [[0],[1,14,15,16,17,18,4,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 6 (.system [[0],[1,14,15,16,17,18,19,4,3],[2],[5],[6],[13]]) (.forbid 1 5 1 (.system [[0],[1,14,5,4,3],[2],[6,7,8,9,10,11,12,13]]) (.forbid 1 6 1 (.system [[0],[1,14,6,7,8,9,10,11,12,13],[2],[3,4,5]]) (.forbid 1 6 2 (.system [[0],[1,14,15,6,7,8,9,10,11,12,13],[2],[3],[5]]) (.forbid 1 6 3 (.system [[0],[1,14,15,16,6,7,8,9,10,11,12,13],[2],[3],[5]]) (.forbid 1 6 4 (.system [[0],[1,14,15,16,17,6,7,8,9,10,11,12,13],[2],[3],[5]]) (.forbid 1 6 5 (.system [[0],[1,14,15,16,17,18,6,7,8,9,10,11,12,13],[2],[3],[5]]) (.forbid 1 6 6 (.system [[0],[1,14,15,16,17,18,19,6,7,8,9,10,11,12,13],[2],[3],[5]]) (.forbid 2 3 1 (.system [[0],[1],[2,14,3,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 2 3 2 (.system [[0],[1],[2,14,15,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 3 3 (.system [[0],[1],[2,14,15,16,3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 2 3 4 (.system [[0],[1],[2,14,15,16,17,3],[5],[6,7,8,9,10,11,12,13]]) (certificate_1181_part_1))))))))))))))))))))

noncomputable def certificate_1181_part_3 : FiniteCertificate := .forbid 0 4 3 (.system [[0,14,15,16,4,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[1],[2],[5],[6],[13]]) (.forbid 0 5 1 (.system [[0,14,5,4,3],[1],[2],[6,7,8,9,10,11,12,13]]) (.forbid 0 6 1 (.system [[0,14,6,7,8,9,10,11,12,13],[1],[2],[3,4,5]]) (.forbid 0 6 2 (.system [[0,14,15,6,7,8,9,10,11,12,13],[1],[2],[3],[5]]) (.forbid 0 6 3 (.system [[0,14,15,16,6,7,8,9,10,11,12,13],[1],[2],[3],[5]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,7,8,9,10,11,12,13],[1],[2],[3],[5]]) (.forbid 0 6 5 (.system [[0,14,15,16,17,18,6,7,8,9,10,11,12,13],[1],[2],[3],[5]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,7,8,9,10,11,12,13],[1],[2],[3],[5]]) (.forbid 1 2 1 (.system [[0],[1,14,2],[3,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,4,5],[2],[6,7,8,9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0],[1,14,15,3],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0],[1,14,15,16,3],[2],[5],[6,7,8,9,10,11,12,13]]) (certificate_1181_part_2))))))))))))))))))))

noncomputable def certificate_1181 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2],[3,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1],[2],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 1 (.system [[0,14,2],[1],[3,4,5],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2],[1],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2],[1],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2],[1],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2],[1],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2],[1],[3],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 1 (.system [[0,14,3,4,5],[1],[2],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 4 1 (.system [[0,14,4,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[1],[2],[5],[6,7,8,9,10,11,12,13]]) (certificate_1181_part_3))))))))))))))))))))

noncomputable def certificate_1183_part_1 : FiniteCertificate := .forbid 2 4 1 (.system [[0],[1],[2,10,4,3],[5,6,7],[9]]) (.forbid 2 4 2 (.system [[0],[1],[2,10,11,4,3],[5],[7],[9]]) (.forbid 2 4 3 (.system [[0],[1],[2,10,11,12,4,3],[5],[7],[9]]) (.forbid 2 4 4 (.system [[0],[1],[2,10,11,12,13,4,3],[5],[7],[9]]) (.forbid 2 4 5 (.system [[0],[1],[2,10,11,12,13,14,4,3],[5],[7],[9]]) (.forbid 2 4 6 (.system [[0],[1],[2,10,11,12,13,14,15,4,3],[5],[7],[9]]) (.forbid 2 6 1 (.system [[0],[1],[2,10,6,5,4,3],[7],[9]]) (.forbid 2 6 2 (.system [[0],[1],[2,10,11,6,5],[3],[7],[9]]) (.forbid 2 6 3 (.system [[0],[1],[2,10,11,12,6,5],[3],[7],[9]]) (.forbid 2 6 4 (.system [[0],[1],[2,10,11,12,13,6,5],[3],[7],[9]]) (.forbid 2 6 5 (.system [[0],[1],[2,10,11,12,13,14,6,5],[3],[7],[9]]) (.forbid 2 6 6 (.system [[0],[1],[2,10,11,12,13,14,15,6,5],[3],[7],[9]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,10,4,5,6,7],[9]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,10,11,4,5],[7],[9]]) (.forbid 3 4 3 (.system [[0],[1],[2],[3,10,11,12,4,5],[7],[9]]) (.forbid 3 4 4 (.system [[0],[1],[2],[3,10,11,12,13,4,5],[7],[9]]) (.forbid 3 4 5 (.system [[0],[1],[2],[3,10,11,12,13,14,4,5],[7],[9]]) (.forbid 3 4 6 (.system [[0],[1],[2],[3,10,11,12,13,14,15,4,5],[7],[9]]) (.forbid 3 6 1 (.system [[0],[1],[2],[3,10,6,5],[7,8,9]]) (.forbid 3 6 2 (.system [[0],[1],[2],[3,10,11,6,5],[7],[9]]) (certificate_1183_part_0))))))))))))))))))))

noncomputable def certificate_1183_part_2 : FiniteCertificate := .forbid 1 3 5 (.system [[0],[1,10,11,12,13,14,3],[2],[5],[7],[9]]) (.forbid 1 3 6 (.system [[0],[1,10,11,12,13,14,15,3],[2],[5],[7],[9]]) (.forbid 1 4 1 (.system [[0],[1,10,4,3],[2],[5,6,7],[9]]) (.forbid 1 4 2 (.system [[0],[1,10,11,4,3],[2],[5],[7],[9]]) (.forbid 1 4 3 (.system [[0],[1,10,11,12,4,3],[2],[5],[7],[9]]) (.forbid 1 4 4 (.system [[0],[1,10,11,12,13,4,3],[2],[5],[7],[9]]) (.forbid 1 4 5 (.system [[0],[1,10,11,12,13,14,4,3],[2],[5],[7],[9]]) (.forbid 1 4 6 (.system [[0],[1,10,11,12,13,14,15,4,3],[2],[5],[7],[9]]) (.forbid 1 6 1 (.system [[0],[1,10,6,5,4,3],[2],[7],[9]]) (.forbid 1 6 2 (.system [[0],[1,10,11,6,5],[2],[3],[7],[9]]) (.forbid 1 6 3 (.system [[0],[1,10,11,12,6,5],[2],[3],[7],[9]]) (.forbid 1 6 4 (.system [[0],[1,10,11,12,13,6,5],[2],[3],[7],[9]]) (.forbid 1 6 5 (.system [[0],[1,10,11,12,13,14,6,5],[2],[3],[7],[9]]) (.forbid 1 6 6 (.system [[0],[1,10,11,12,13,14,15,6,5],[2],[3],[7],[9]]) (.forbid 2 3 1 (.system [[0],[1],[2,10,3,4,5,6,7,8,9]]) (.forbid 2 3 2 (.system [[0],[1],[2,10,11,3,4,5],[7],[9]]) (.forbid 2 3 3 (.system [[0],[1],[2,10,11,12,3],[5],[7],[9]]) (.forbid 2 3 4 (.system [[0],[1],[2,10,11,12,13,3],[5],[7],[9]]) (.forbid 2 3 5 (.system [[0],[1],[2,10,11,12,13,14,3],[5],[7],[9]]) (.forbid 2 3 6 (.system [[0],[1],[2,10,11,12,13,14,15,3],[5],[7],[9]]) (certificate_1183_part_1))))))))))))))))))))

noncomputable def certificate_1183_part_3 : FiniteCertificate := .forbid 0 4 3 (.system [[0,10,11,12,4,3],[1],[2],[5],[7],[9]]) (.forbid 0 4 4 (.system [[0,10,11,12,13,4,3],[1],[2],[5],[7],[9]]) (.forbid 0 4 5 (.system [[0,10,11,12,13,14,4,3],[1],[2],[5],[7],[9]]) (.forbid 0 4 6 (.system [[0,10,11,12,13,14,15,4,3],[1],[2],[5],[7],[9]]) (.forbid 0 6 1 (.system [[0,10,6,5,4,3],[1],[2],[7],[9]]) (.forbid 0 6 2 (.system [[0,10,11,6,5],[1],[2],[3],[7],[9]]) (.forbid 0 6 3 (.system [[0,10,11,12,6,5],[1],[2],[3],[7],[9]]) (.forbid 0 6 4 (.system [[0,10,11,12,13,6,5],[1],[2],[3],[7],[9]]) (.forbid 0 6 5 (.system [[0,10,11,12,13,14,6,5],[1],[2],[3],[7],[9]]) (.forbid 0 6 6 (.system [[0,10,11,12,13,14,15,6,5],[1],[2],[3],[7],[9]]) (.forbid 1 2 1 (.system [[0],[1,10,2],[3,4,5,6,7,8,9]]) (.forbid 1 2 2 (.system [[0],[1,10,11,2],[3,4,5],[7],[9]]) (.forbid 1 2 3 (.system [[0],[1,10,11,12,2],[3],[5],[7],[9]]) (.forbid 1 2 4 (.system [[0],[1,10,11,12,13,2],[3],[5],[7],[9]]) (.forbid 1 2 5 (.system [[0],[1,10,11,12,13,14,2],[3],[5],[7],[9]]) (.forbid 1 2 6 (.system [[0],[1,10,11,12,13,14,15,2],[3],[5],[7],[9]]) (.forbid 1 3 1 (.system [[0],[1,10,3,4,5,6,7,8,9],[2]]) (.forbid 1 3 2 (.system [[0],[1,10,11,3,4,5],[2],[7],[9]]) (.forbid 1 3 3 (.system [[0],[1,10,11,12,3],[2],[5],[7],[9]]) (.forbid 1 3 4 (.system [[0],[1,10,11,12,13,3],[2],[5],[7],[9]]) (certificate_1183_part_2))))))))))))))))))))

noncomputable def certificate_1183 : FiniteCertificate := .forbid 0 1 1 (.system [[0,10,1],[2],[3,4,5,6,7,8,9]]) (.forbid 0 1 2 (.system [[0,10,11,1],[2],[3,4,5],[7],[9]]) (.forbid 0 1 3 (.system [[0,10,11,12,1],[2],[3],[5],[7],[9]]) (.forbid 0 1 4 (.system [[0,10,11,12,13,1],[2],[3],[5],[7],[9]]) (.forbid 0 1 5 (.system [[0,10,11,12,13,14,1],[2],[3],[5],[7],[9]]) (.forbid 0 1 6 (.system [[0,10,11,12,13,14,15,1],[2],[3],[5],[7],[9]]) (.forbid 0 2 1 (.system [[0,10,2],[1],[3,4,5,6,7,8,9]]) (.forbid 0 2 2 (.system [[0,10,11,2],[1],[3,4,5],[7],[9]]) (.forbid 0 2 3 (.system [[0,10,11,12,2],[1],[3],[5],[7],[9]]) (.forbid 0 2 4 (.system [[0,10,11,12,13,2],[1],[3],[5],[7],[9]]) (.forbid 0 2 5 (.system [[0,10,11,12,13,14,2],[1],[3],[5],[7],[9]]) (.forbid 0 2 6 (.system [[0,10,11,12,13,14,15,2],[1],[3],[5],[7],[9]]) (.forbid 0 3 1 (.system [[0,10,3,4,5,6,7,8,9],[1],[2]]) (.forbid 0 3 2 (.system [[0,10,11,3,4,5],[1],[2],[7],[9]]) (.forbid 0 3 3 (.system [[0,10,11,12,3],[1],[2],[5],[7],[9]]) (.forbid 0 3 4 (.system [[0,10,11,12,13,3],[1],[2],[5],[7],[9]]) (.forbid 0 3 5 (.system [[0,10,11,12,13,14,3],[1],[2],[5],[7],[9]]) (.forbid 0 3 6 (.system [[0,10,11,12,13,14,15,3],[1],[2],[5],[7],[9]]) (.forbid 0 4 1 (.system [[0,10,4,3],[1],[2],[5,6,7],[9]]) (.forbid 0 4 2 (.system [[0,10,11,4,3],[1],[2],[5],[7],[9]]) (certificate_1183_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates038
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1211_part_2 : FiniteCertificate := .forbid 1 3 4 (.system [[0],[1,14,15,16,17,3],[2],[6],[8,9,10,11,12,13]]) (.forbid 1 3 5 (.system [[0],[1,14,15,16,17,18,3,4,5,6],[2],[8],[13]]) (.forbid 1 3 6 (.system [[0],[1,14,15,16,17,18,19,3,4,5,6],[2],[8],[13]]) (.forbid 1 4 1 (.system [[0],[1,14,4,5,6],[2],[3],[8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4,3],[2],[6],[8,9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0],[1,14,15,16,4,3],[2],[6],[8,9,10,11,12,13]]) (.forbid 1 4 4 (.system [[0],[1,14,15,16,17,4,3],[2],[6],[8,9,10,11,12,13]]) (.forbid 1 4 5 (.system [[0],[1,14,15,16,17,18,4,3],[2],[6,7,8],[13]]) (.forbid 1 4 6 (.system [[0],[1,14,15,16,17,18,19,4,3],[2],[6],[8],[13]]) (.forbid 1 5 1 (.system [[0],[1,14,5,4,3],[2],[6],[8,9,10,11,12,13]]) (.forbid 1 7 1 (.system [[0],[1,14,7,6,5,4,3],[2],[8,9,10,11,12,13]]) (.forbid 1 7 2 (.system [[0],[1,14,15,7,6],[2],[3],[8,9,10,11,12,13]]) (.forbid 1 7 3 (.system [[0],[1,14,15,16,7,6],[2],[3],[8,9,10,11,12,13]]) (.forbid 1 7 4 (.system [[0],[1,14,15,16,17,7,6,5,4,3],[2],[8],[13]]) (.forbid 1 7 5 (.system [[0],[1,14,15,16,17,18,7,6,5,4,3],[2],[8],[13]]) (.forbid 1 7 6 (.system [[0],[1,14,15,16,17,18,19,7,6],[2],[3],[8],[13]]) (.forbid 2 3 1 (.system [[0],[1],[2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 3 2 (.system [[0],[1],[2,14,15,3,4,5,6],[8,9,10,11,12,13]]) (.forbid 2 3 3 (.system [[0],[1],[2,14,15,16,3],[6],[8,9,10,11,12,13]]) (.forbid 2 3 4 (.system [[0],[1],[2,14,15,16,17,3],[6],[8,9,10,11,12,13]]) (certificate_1211_part_1))))))))))))))))))))

noncomputable def certificate_1211_part_3 : FiniteCertificate := .forbid 0 4 3 (.system [[0,14,15,16,4,3],[1],[2],[6],[8,9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[1],[2],[6],[8,9,10,11,12,13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3],[1],[2],[6,7,8],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[1],[2],[6],[8],[13]]) (.forbid 0 5 1 (.system [[0,14,5,4,3],[1],[2],[6],[8,9,10,11,12,13]]) (.forbid 0 7 1 (.system [[0,14,7,6,5,4,3],[1],[2],[8,9,10,11,12,13]]) (.forbid 0 7 2 (.system [[0,14,15,7,6],[1],[2],[3],[8,9,10,11,12,13]]) (.forbid 0 7 3 (.system [[0,14,15,16,7,6],[1],[2],[3],[8,9,10,11,12,13]]) (.forbid 0 7 4 (.system [[0,14,15,16,17,7,6,5,4,3],[1],[2],[8],[13]]) (.forbid 0 7 5 (.system [[0,14,15,16,17,18,7,6,5,4,3],[1],[2],[8],[13]]) (.forbid 0 7 6 (.system [[0,14,15,16,17,18,19,7,6],[1],[2],[3],[8],[13]]) (.forbid 1 2 1 (.system [[0],[1,14,2],[3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2],[3,4,5,6],[8,9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2],[3],[6],[8,9,10,11,12,13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2],[3],[6],[8,9,10,11,12,13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2],[3,4,5,6],[8],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2],[3,4,5,6],[8],[13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,4,5,6,7,8,9,10,11,12,13],[2]]) (.forbid 1 3 2 (.system [[0],[1,14,15,3,4,5,6],[2],[8,9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0],[1,14,15,16,3],[2],[6],[8,9,10,11,12,13]]) (certificate_1211_part_2))))))))))))))))))))

noncomputable def certificate_1211 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2],[3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[2],[3,4,5,6],[8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[2],[3],[6],[8,9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[2],[3],[6],[8,9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[2],[3,4,5,6],[8],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1],[2],[3,4,5,6],[8],[13]]) (.forbid 0 2 1 (.system [[0,14,2],[1],[3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2],[1],[3,4,5,6],[8,9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2],[1],[3],[6],[8,9,10,11,12,13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2],[1],[3],[6],[8,9,10,11,12,13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2],[1],[3,4,5,6],[8],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2],[1],[3,4,5,6],[8],[13]]) (.forbid 0 3 1 (.system [[0,14,3,4,5,6,7,8,9,10,11,12,13],[1],[2]]) (.forbid 0 3 2 (.system [[0,14,15,3,4,5,6],[1],[2],[8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3],[1],[2],[6],[8,9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[1],[2],[6],[8,9,10,11,12,13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,4,5,6],[1],[2],[8],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,4,5,6],[1],[2],[8],[13]]) (.forbid 0 4 1 (.system [[0,14,4,5,6],[1],[2],[3],[8,9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[1],[2],[6],[8,9,10,11,12,13]]) (certificate_1211_part_3))))))))))))))))))))

noncomputable def certificate_1212_part_1 : FiniteCertificate := .forbid 3 4 3 (.system [[0],[1],[2],[3,15,16,17,4,5,6],[8,9,10,11,12,13,14]]) (.forbid 3 4 4 (.system [[0],[1],[2],[3,15,16,17,18,4,5,6],[8,9,10,11,12,13,14]]) (.forbid 3 4 5 (.system [[0],[1],[2],[3,15,16,17,18,19,4,5,6,7,8],[14]]) (.forbid 3 4 6 (.system [[0],[1],[2],[3,15,16,17,18,19,20,4,5,6],[8],[14]]) (.forbid 3 7 1 (.system [[0],[1],[2],[6,5,4,3,15,7,8,9,10,11,12,13,14]]) (.forbid 3 7 2 (.system [[0],[1],[2],[3,15,16,7,6],[8,9,10,11,12,13,14]]) (.forbid 3 7 3 (.system [[0],[1],[2],[3,15,16,17,7,6],[8,9,10,11,12,13,14]]) (.forbid 3 7 4 (.system [[0],[1],[2],[3,15,16,17,18,7,6],[8,9,10,11,12,13,14]]) (.forbid 3 7 5 (.system [[0],[1],[2],[3,15,16,17,18,19,7,6],[8,9,10,11,12,13,14]]) (.forbid 3 7 6 (.system [[0],[1],[2],[3,15,16,17,18,19,20,7,6],[8,9,10,11,12,13,14]]) (.forbid 3 9 1 (.system [[0],[1],[2],[6,5,4,3,15,9,10,11,12,13,14],[8]]) (.forbid 3 13 1 (.system [[0],[1],[2],[6,5,4,3,15,13,12,11,10,9,8],[14]]) (.forbid 4 5 1 (.system [[0],[1],[2],[3,4,15,5,6],[8,9,10,11,12,13,14]]) (.forbid 4 7 1 (.system [[0],[1],[2],[3,4,15,7,6],[8,9,10,11,12,13,14]]) (.forbid 4 7 2 (.system [[0],[1],[2],[3,4,15,16,7,6],[8,9,10,11,12,13,14]]) (.forbid 4 7 3 (.system [[0],[1],[2],[3,4,15,16,17,7,6],[8,9,10,11,12,13,14]]) (.forbid 4 7 4 (.system [[0],[1],[2],[3,4,15,16,17,18,7,6],[8,9,10,11,12,13,14]]) (.forbid 4 7 5 (.system [[0],[1],[2],[3,4,15,16,17,18,19,7,6],[8,9,10,11,12,13,14]]) (.forbid 4 7 6 (.system [[0],[1],[2],[3,4,15,16,17,18,19,20,7,6],[8],[14]]) (.forbid 4 8 1 (.system [[0],[1],[2],[3],[6,5,4,15,8,9,10,11,12,13,14]]) (certificate_1212_part_0))))))))))))))))))))

noncomputable def certificate_1212_part_2 : FiniteCertificate := .forbid 2 3 3 (.system [[0],[1],[2,15,16,17,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 3 4 (.system [[0],[1],[2,15,16,17,18,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 3 5 (.system [[0],[1],[2,15,16,17,18,19,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 3 6 (.system [[0],[1],[2,15,16,17,18,19,20,3,4,5,6],[8],[14]]) (.forbid 2 4 1 (.system [[0],[1],[2,15,4,5,6],[3],[8,9,10,11,12,13,14]]) (.forbid 2 4 2 (.system [[0],[1],[2,15,16,4,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 4 3 (.system [[0],[1],[2,15,16,17,4,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 4 4 (.system [[0],[1],[2,15,16,17,18,4,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 4 5 (.system [[0],[1],[2,15,16,17,18,19,4,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 4 6 (.system [[0],[1],[2,15,16,17,18,19,20,4,3],[6,7,8],[14]]) (.forbid 2 5 1 (.system [[0],[1],[2,15,5,4,3],[6],[8,9,10,11,12,13,14]]) (.forbid 2 7 1 (.system [[0],[1],[2,15,7,6,5,4,3],[8,9,10,11,12,13,14]]) (.forbid 2 7 2 (.system [[0],[1],[2,15,16,7,6],[3],[8,9,10,11,12,13,14]]) (.forbid 2 7 3 (.system [[0],[1],[2,15,16,17,7,6],[3],[8,9,10,11,12,13,14]]) (.forbid 2 7 4 (.system [[0],[1],[2,15,16,17,18,7,6],[3],[8,9,10,11,12,13,14]]) (.forbid 2 7 5 (.system [[0],[1],[2,15,16,17,18,19,7,6,5,4,3],[8],[14]]) (.forbid 2 7 6 (.system [[0],[1],[2,15,16,17,18,19,20,7,6,5,4,3],[8],[14]]) (.forbid 2 9 1 (.system [[0],[1],[2,15,9,10,11,12,13,14],[3,4,5,6],[8]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,15,4,5,6],[8,9,10,11,12,13,14]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,15,16,4,5,6],[8,9,10,11,12,13,14]]) (certificate_1212_part_1))))))))))))))))))))

noncomputable def certificate_1212_part_3 : FiniteCertificate := .forbid 1 3 3 (.system [[0],[1,15,16,17,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 3 4 (.system [[0],[1,15,16,17,18,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 3 5 (.system [[0],[1,15,16,17,18,19,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 3 6 (.system [[0],[1,15,16,17,18,19,20,3,4,5,6],[2],[8],[14]]) (.forbid 1 4 1 (.system [[0],[1,15,4,5,6],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 1 4 2 (.system [[0],[1,15,16,4,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 4 3 (.system [[0],[1,15,16,17,4,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 4 4 (.system [[0],[1,15,16,17,18,4,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 4 5 (.system [[0],[1,15,16,17,18,19,4,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 4 6 (.system [[0],[1,15,16,17,18,19,20,4,3],[2],[6,7,8],[14]]) (.forbid 1 5 1 (.system [[0],[1,15,5,4,3],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 1 7 1 (.system [[0],[1,15,7,6,5,4,3],[2],[8,9,10,11,12,13,14]]) (.forbid 1 7 2 (.system [[0],[1,15,16,7,6],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 1 7 3 (.system [[0],[1,15,16,17,7,6],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 1 7 4 (.system [[0],[1,15,16,17,18,7,6],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 1 7 5 (.system [[0],[1,15,16,17,18,19,7,6,5,4,3],[2],[8],[14]]) (.forbid 1 7 6 (.system [[0],[1,15,16,17,18,19,20,7,6,5,4,3],[2],[8],[14]]) (.forbid 1 9 1 (.system [[0],[1,15,9,10,11,12,13,14],[2],[3,4,5,6],[8]]) (.forbid 2 3 1 (.system [[0],[1],[2,15,3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 2 3 2 (.system [[0],[1],[2,15,16,3,4,5,6],[8,9,10,11,12,13,14]]) (certificate_1212_part_2))))))))))))))))))))

noncomputable def certificate_1212_part_4 : FiniteCertificate := .forbid 0 4 3 (.system [[0,15,16,17,4,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 4 4 (.system [[0,15,16,17,18,4,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 4 5 (.system [[0,15,16,17,18,19,4,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 4 6 (.system [[0,15,16,17,18,19,20,4,3],[1],[2],[6,7,8],[14]]) (.forbid 0 5 1 (.system [[0,15,5,4,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 7 1 (.system [[0,15,7,6,5,4,3],[1],[2],[8,9,10,11,12,13,14]]) (.forbid 0 7 2 (.system [[0,15,16,7,6],[1],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 0 7 3 (.system [[0,15,16,17,7,6],[1],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 0 7 4 (.system [[0,15,16,17,18,7,6],[1],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 0 7 5 (.system [[0,15,16,17,18,19,7,6,5,4,3],[1],[2],[8],[14]]) (.forbid 0 7 6 (.system [[0,15,16,17,18,19,20,7,6,5,4,3],[1],[2],[8],[14]]) (.forbid 0 9 1 (.system [[0,15,9,10,11,12,13,14],[1],[2],[3,4,5,6],[8]]) (.forbid 1 2 1 (.system [[0],[1,15,2],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 1 2 2 (.system [[0],[1,15,16,2],[3,4,5,6],[8,9,10,11,12,13,14]]) (.forbid 1 2 3 (.system [[0],[1,15,16,17,2],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 1 2 4 (.system [[0],[1,15,16,17,18,2],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 1 2 5 (.system [[0],[1,15,16,17,18,19,2],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 1 2 6 (.system [[0],[1,15,16,17,18,19,20,2],[3,4,5,6],[8],[14]]) (.forbid 1 3 1 (.system [[0],[1,15,3,4,5,6,7,8,9,10,11,12,13,14],[2]]) (.forbid 1 3 2 (.system [[0],[1,15,16,3,4,5,6],[2],[8,9,10,11,12,13,14]]) (certificate_1212_part_3))))))))))))))))))))

noncomputable def certificate_1212 : FiniteCertificate := .forbid 0 1 1 (.system [[0,15,1],[2],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 2 (.system [[0,15,16,1],[2],[3,4,5,6],[8,9,10,11,12,13,14]]) (.forbid 0 1 3 (.system [[0,15,16,17,1],[2],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 0 1 4 (.system [[0,15,16,17,18,1],[2],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 0 1 5 (.system [[0,15,16,17,18,19,1],[2],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 0 1 6 (.system [[0,15,16,17,18,19,20,1],[2],[3,4,5,6],[8],[14]]) (.forbid 0 2 1 (.system [[0,15,2],[1],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 2 2 (.system [[0,15,16,2],[1],[3,4,5,6],[8,9,10,11,12,13,14]]) (.forbid 0 2 3 (.system [[0,15,16,17,2],[1],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 0 2 4 (.system [[0,15,16,17,18,2],[1],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 0 2 5 (.system [[0,15,16,17,18,19,2],[1],[3],[6],[8,9,10,11,12,13,14]]) (.forbid 0 2 6 (.system [[0,15,16,17,18,19,20,2],[1],[3,4,5,6],[8],[14]]) (.forbid 0 3 1 (.system [[0,15,3,4,5,6,7,8,9,10,11,12,13,14],[1],[2]]) (.forbid 0 3 2 (.system [[0,15,16,3,4,5,6],[1],[2],[8,9,10,11,12,13,14]]) (.forbid 0 3 3 (.system [[0,15,16,17,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 3 4 (.system [[0,15,16,17,18,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 3 5 (.system [[0,15,16,17,18,19,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (.forbid 0 3 6 (.system [[0,15,16,17,18,19,20,3,4,5,6],[1],[2],[8],[14]]) (.forbid 0 4 1 (.system [[0,15,4,5,6],[1],[2],[3],[8,9,10,11,12,13,14]]) (.forbid 0 4 2 (.system [[0,15,16,4,3],[1],[2],[6],[8,9,10,11,12,13,14]]) (certificate_1212_part_4))))))))))))))))))))

noncomputable def certificate_1215_part_1 : FiniteCertificate := .forbid 4 5 1 (.system [[0],[1],[2],[3,4,15,5,6,7,8,9,10,11,12,13,14]]) (.forbid 4 5 2 (.system [[0],[1],[2],[3,4,15,16,5,6],[9,10,11,12,13,14]]) (.forbid 4 5 3 (.system [[0],[1],[2],[3,4,15,16,17,5,6],[9,10,11,12,13,14]]) (.forbid 4 5 4 (.system [[0],[1],[2],[3,4,15,16,17,18,5,6,7,8,9],[14]]) (.forbid 4 5 5 (.system [[0],[1],[2],[3,4,15,16,17,18,19,5,6,7,8,9],[14]]) (.forbid 4 5 6 (.system [[0],[1],[2],[3,4,15,16,17,18,19,20,5,6],[9],[14]]) (.forbid 4 7 1 (.system [[0],[1],[2],[3,4,15,7,8,9,10,11,12,13,14],[6]]) (.forbid 4 7 2 (.system [[0],[1],[2],[3,4,15,16,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 3 (.system [[0],[1],[2],[3,4,15,16,17,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 4 (.system [[0],[1],[2],[3,4,15,16,17,18,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 5 (.system [[0],[1],[2],[3,4,15,16,17,18,19,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 6 (.system [[0],[1],[2],[3,4,15,16,17,18,19,20,7,6],[9],[14]]) (.forbid 4 8 1 (.system [[0],[1],[2],[3,4,15,8,7,6],[9,10,11,12,13,14]]) (.forbid 5 6 1 (.system [[0],[1],[2],[3,4,5,15,6,7,8,9,10,11,12,13,14]]) (.forbid 5 7 1 (.system [[0],[1],[2],[3,4,5,15,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 2 (.system [[0],[1],[2],[3,4,5,15,16,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 3 (.system [[0],[1],[2],[3,4,5,15,16,17,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 4 (.system [[0],[1],[2],[3,4,5,15,16,17,18,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 5 (.system [[0],[1],[2],[3,4,5,15,16,17,18,19,7,6],[9],[14]]) (.forbid 5 7 6 (.system [[0],[1],[2],[3,4,5,15,16,17,18,19,20,7,6],[9],[14]]) (certificate_1215_part_0))))))))))))))))))))

noncomputable def certificate_1215_part_2 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1],[2,15,16,4,3],[6,7,8,9,10,11,12,13,14]]) (.forbid 2 4 3 (.system [[0],[1],[2,15,16,17,4,3],[6],[9,10,11,12,13,14]]) (.forbid 2 4 4 (.system [[0],[1],[2,15,16,17,18,4,3],[6],[9,10,11,12,13,14]]) (.forbid 2 4 5 (.system [[0],[1],[2,15,16,17,18,19,4,3],[6,7,8,9],[14]]) (.forbid 2 4 6 (.system [[0],[1],[2,15,16,17,18,19,20,4,3],[6,7,8,9],[14]]) (.forbid 2 5 1 (.system [[0],[1],[2,15,5,4,3],[6,7,8,9,10,11,12,13,14]]) (.forbid 2 5 2 (.system [[0],[1],[2,15,16,5,4,3],[6],[9,10,11,12,13,14]]) (.forbid 2 5 3 (.system [[0],[1],[2,15,16,17,5,4,3],[6],[9,10,11,12,13,14]]) (.forbid 2 5 4 (.system [[0],[1],[2,15,16,17,18,5,4,3],[6,7,8,9],[14]]) (.forbid 2 5 5 (.system [[0],[1],[2,15,16,17,18,19,5,4,3],[6,7,8,9],[14]]) (.forbid 2 5 6 (.system [[0],[1],[2,15,16,17,18,19,20,5,4,3],[6],[9],[14]]) (.forbid 2 7 1 (.system [[0],[1],[2,15,7,8,9,10,11,12,13,14],[3,4,5,6]]) (.forbid 2 7 2 (.system [[0],[1],[2,15,16,7,6,5,4,3],[9,10,11,12,13,14]]) (.forbid 2 7 3 (.system [[0],[1],[2,15,16,17,7,6],[3],[9,10,11,12,13,14]]) (.forbid 2 7 4 (.system [[0],[1],[2,15,16,17,18,7,6],[3],[9,10,11,12,13,14]]) (.forbid 2 7 5 (.system [[0],[1],[2,15,16,17,18,19,7,6,5,4,3],[9],[14]]) (.forbid 2 7 6 (.system [[0],[1],[2,15,16,17,18,19,20,7,6,5,4,3],[9],[14]]) (.forbid 2 8 1 (.system [[0],[1],[2,15,8,7,6,5,4,3],[9,10,11,12,13,14]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,15,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 3 7 1 (.system [[0],[1],[2],[6,5,4,3,15,7,8,9,10,11,12,13,14]]) (certificate_1215_part_1))))))))))))))))))))

noncomputable def certificate_1215_part_3 : FiniteCertificate := .forbid 1 4 2 (.system [[0],[1,15,16,4,3],[2],[6,7,8,9,10,11,12,13,14]]) (.forbid 1 4 3 (.system [[0],[1,15,16,17,4,3],[2],[6],[9,10,11,12,13,14]]) (.forbid 1 4 4 (.system [[0],[1,15,16,17,18,4,3],[2],[6],[9,10,11,12,13,14]]) (.forbid 1 4 5 (.system [[0],[1,15,16,17,18,19,4,3],[2],[6,7,8,9],[14]]) (.forbid 1 4 6 (.system [[0],[1,15,16,17,18,19,20,4,3],[2],[6,7,8,9],[14]]) (.forbid 1 5 1 (.system [[0],[1,15,5,4,3],[2],[6,7,8,9,10,11,12,13,14]]) (.forbid 1 5 2 (.system [[0],[1,15,16,5,4,3],[2],[6],[9,10,11,12,13,14]]) (.forbid 1 5 3 (.system [[0],[1,15,16,17,5,4,3],[2],[6],[9,10,11,12,13,14]]) (.forbid 1 5 4 (.system [[0],[1,15,16,17,18,5,4,3],[2],[6,7,8,9],[14]]) (.forbid 1 5 5 (.system [[0],[1,15,16,17,18,19,5,4,3],[2],[6,7,8,9],[14]]) (.forbid 1 5 6 (.system [[0],[1,15,16,17,18,19,20,5,4,3],[2],[6],[9],[14]]) (.forbid 1 7 1 (.system [[0],[1,15,7,8,9,10,11,12,13,14],[2],[3,4,5,6]]) (.forbid 1 7 2 (.system [[0],[1,15,16,7,6,5,4,3],[2],[9,10,11,12,13,14]]) (.forbid 1 7 3 (.system [[0],[1,15,16,17,7,6],[2],[3],[9,10,11,12,13,14]]) (.forbid 1 7 4 (.system [[0],[1,15,16,17,18,7,6],[2],[3],[9,10,11,12,13,14]]) (.forbid 1 7 5 (.system [[0],[1,15,16,17,18,19,7,6,5,4,3],[2],[9],[14]]) (.forbid 1 7 6 (.system [[0],[1,15,16,17,18,19,20,7,6,5,4,3],[2],[9],[14]]) (.forbid 1 8 1 (.system [[0],[1,15,8,7,6,5,4,3],[2],[9,10,11,12,13,14]]) (.forbid 2 3 1 (.system [[0],[1],[2,15,3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 2 4 1 (.system [[0],[1],[2,15,4,5,6,7,8,9,10,11,12,13,14],[3]]) (certificate_1215_part_2))))))))))))))))))))

noncomputable def certificate_1215_part_4 : FiniteCertificate := .forbid 0 5 2 (.system [[0,15,16,5,4,3],[1],[2],[6],[9,10,11,12,13,14]]) (.forbid 0 5 3 (.system [[0,15,16,17,5,4,3],[1],[2],[6],[9,10,11,12,13,14]]) (.forbid 0 5 4 (.system [[0,15,16,17,18,5,4,3],[1],[2],[6,7,8,9],[14]]) (.forbid 0 5 5 (.system [[0,15,16,17,18,19,5,4,3],[1],[2],[6,7,8,9],[14]]) (.forbid 0 5 6 (.system [[0,15,16,17,18,19,20,5,4,3],[1],[2],[6],[9],[14]]) (.forbid 0 7 1 (.system [[0,15,7,8,9,10,11,12,13,14],[1],[2],[3,4,5,6]]) (.forbid 0 7 2 (.system [[0,15,16,7,6,5,4,3],[1],[2],[9,10,11,12,13,14]]) (.forbid 0 7 3 (.system [[0,15,16,17,7,6],[1],[2],[3],[9,10,11,12,13,14]]) (.forbid 0 7 4 (.system [[0,15,16,17,18,7,6],[1],[2],[3],[9,10,11,12,13,14]]) (.forbid 0 7 5 (.system [[0,15,16,17,18,19,7,6,5,4,3],[1],[2],[9],[14]]) (.forbid 0 7 6 (.system [[0,15,16,17,18,19,20,7,6,5,4,3],[1],[2],[9],[14]]) (.forbid 0 8 1 (.system [[0,15,8,7,6,5,4,3],[1],[2],[9,10,11,12,13,14]]) (.forbid 1 2 1 (.system [[0],[1,15,2],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 1 2 2 (.system [[0],[1,15,16,2],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 1 2 3 (.system [[0],[1,15,16,17,2],[3,4,5,6],[9,10,11,12,13,14]]) (.forbid 1 2 4 (.system [[0],[1,15,16,17,18,2],[3],[6],[9,10,11,12,13,14]]) (.forbid 1 2 5 (.system [[0],[1,15,16,17,18,19,2],[3],[6],[9,10,11,12,13,14]]) (.forbid 1 2 6 (.system [[0],[1,15,16,17,18,19,20,2],[3,4,5,6],[9],[14]]) (.forbid 1 3 1 (.system [[0],[1,15,3,4,5,6,7,8,9,10,11,12,13,14],[2]]) (.forbid 1 4 1 (.system [[0],[1,15,4,5,6,7,8,9,10,11,12,13,14],[2],[3]]) (certificate_1215_part_3))))))))))))))))))))

noncomputable def certificate_1215 : FiniteCertificate := .forbid 0 1 1 (.system [[0,15,1],[2],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 2 (.system [[0,15,16,1],[2],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 3 (.system [[0,15,16,17,1],[2],[3,4,5,6],[9,10,11,12,13,14]]) (.forbid 0 1 4 (.system [[0,15,16,17,18,1],[2],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 1 5 (.system [[0,15,16,17,18,19,1],[2],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 1 6 (.system [[0,15,16,17,18,19,20,1],[2],[3,4,5,6],[9],[14]]) (.forbid 0 2 1 (.system [[0,15,2],[1],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 2 2 (.system [[0,15,16,2],[1],[3,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 2 3 (.system [[0,15,16,17,2],[1],[3,4,5,6],[9,10,11,12,13,14]]) (.forbid 0 2 4 (.system [[0,15,16,17,18,2],[1],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 2 5 (.system [[0,15,16,17,18,19,2],[1],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 2 6 (.system [[0,15,16,17,18,19,20,2],[1],[3,4,5,6],[9],[14]]) (.forbid 0 3 1 (.system [[0,15,3,4,5,6,7,8,9,10,11,12,13,14],[1],[2]]) (.forbid 0 4 1 (.system [[0,15,4,5,6,7,8,9,10,11,12,13,14],[1],[2],[3]]) (.forbid 0 4 2 (.system [[0,15,16,4,3],[1],[2],[6,7,8,9,10,11,12,13,14]]) (.forbid 0 4 3 (.system [[0,15,16,17,4,3],[1],[2],[6],[9,10,11,12,13,14]]) (.forbid 0 4 4 (.system [[0,15,16,17,18,4,3],[1],[2],[6],[9,10,11,12,13,14]]) (.forbid 0 4 5 (.system [[0,15,16,17,18,19,4,3],[1],[2],[6,7,8,9],[14]]) (.forbid 0 4 6 (.system [[0,15,16,17,18,19,20,4,3],[1],[2],[6,7,8,9],[14]]) (.forbid 0 5 1 (.system [[0,15,5,4,3],[1],[2],[6,7,8,9,10,11,12,13,14]]) (certificate_1215_part_4))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates039
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1221_part_1_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((0,1,2) :: (((0,1,1) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (certificate_1221_M))))))))))))))))

noncomputable def certificate_1221_part_2_M : ForbiddenMatrix := ((0,3,6) :: (((0,3,5) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,2,2) :: (((0,2,1) :: (((0,1,6) :: (certificate_1221_part_1_M))))))))))))))))

noncomputable def certificate_1221_part_3_M : ForbiddenMatrix := ((0,5,3) :: (((0,5,2) :: (((0,4,6) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_1221_part_2_M))))))))))))))))

noncomputable def certificate_1221_part_4_M : ForbiddenMatrix := ((1,2,4) :: (((1,2,2) :: (((1,2,1) :: (((0,7,1) :: (((0,6,1) :: (((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (certificate_1221_part_3_M))))))))))))))))

noncomputable def certificate_1221_part_5_M : ForbiddenMatrix := ((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,6) :: (((1,2,5) :: (certificate_1221_part_4_M))))))))))))))))

noncomputable def certificate_1221_part_6_M : ForbiddenMatrix := ((1,5,3) :: (((1,5,2) :: (((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (certificate_1221_part_5_M))))))))))))))))

noncomputable def certificate_1221_part_7_M : ForbiddenMatrix := ((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,7,1) :: (((1,6,1) :: (((1,5,6) :: (((1,5,5) :: (((1,5,4) :: (certificate_1221_part_6_M))))))))))))))))

noncomputable def certificate_1221_part_8_M : ForbiddenMatrix := ((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (certificate_1221_part_7_M))))))))))))))))

noncomputable def certificate_1221_part_9_M : ForbiddenMatrix := ((2,7,1) :: (((2,6,1) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (((2,5,2) :: (((2,4,6) :: (certificate_1221_part_8_M))))))))))))))))

noncomputable def certificate_1221_part_10_M : ForbiddenMatrix := ((3,5,3) :: (((3,5,2) :: (((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (certificate_1221_part_9_M))))))))))))))))

noncomputable def certificate_1221_part_11_M : ForbiddenMatrix := ((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,5,6) :: (((3,5,5) :: (((3,5,4) :: (certificate_1221_part_10_M))))))))))))))))

noncomputable def certificate_1221_part_12_M : ForbiddenMatrix := ((0,5,1) :: (((0,2,3) :: (((0,1,3) :: (((5,6,1) :: (((4,9,1) :: (((4,8,1) :: (((4,5,6) :: (certificate_1221_part_11_M))))))))))))))

noncomputable def certificate_1221_part_13_M : ForbiddenMatrix := ((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,4,0) :: (((5,6,1) :: (((4,9,1) :: (((4,8,1) :: (((4,5,6) :: (certificate_1221_part_11_M))))))))))))))))

noncomputable def certificate_1221_part_14_M : ForbiddenMatrix := ((1,6,6) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((0,8,1) :: (((0,6,6) :: (((0,6,5) :: (certificate_1221_part_13_M))))))))))))))))

noncomputable def certificate_1221_part_15_M : ForbiddenMatrix := ((3,6,3) :: (((2,8,1) :: (((2,6,6) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (((2,6,2) :: (((1,8,1) :: (certificate_1221_part_14_M))))))))))))))))

noncomputable def certificate_1221_part_16_M : ForbiddenMatrix := ((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((3,9,1) :: (((3,8,1) :: (((3,6,6) :: (((3,6,5) :: (((3,6,4) :: (certificate_1221_part_15_M))))))))))))))))

noncomputable def certificate_1221_part_17_M : ForbiddenMatrix := ((3,6,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((6,7,1) :: (((4,6,6) :: (((4,6,5) :: (certificate_1221_part_16_M))))))))))))))

noncomputable def certificate_1221_part_18_M : ForbiddenMatrix := ((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,5,0) :: (((6,7,1) :: (((4,6,6) :: (((4,6,5) :: (certificate_1221_part_16_M))))))))))))))))

noncomputable def certificate_1221_part_19_M : ForbiddenMatrix := ((1,9,1) :: (((1,7,6) :: (((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,7,2) :: (((0,9,1) :: (((0,7,6) :: (certificate_1221_part_18_M))))))))))))))))

noncomputable def certificate_1221_part_20_M : ForbiddenMatrix := ((6,7,3) :: (((6,7,2) :: (((4,7,5) :: (((4,7,4) :: (((4,7,3) :: (((3,7,6) :: (((3,7,5) :: (((3,7,4) :: (certificate_1221_part_19_M))))))))))))))))

noncomputable def certificate_1221_part_21_M : ForbiddenMatrix := ((1,4,0) :: (((0,6,0) :: (((0,1,3) :: (((7,9,1) :: (((7,8,1) :: (((6,7,5) :: (((6,7,4) :: (certificate_1221_part_20_M))))))))))))))

noncomputable def certificate_1221_part_22_M : ForbiddenMatrix := ((3,7,2) :: (((3,7,1) :: (((3,6,2) :: (((3,6,1) :: (((3,6,0) :: (((2,6,0) :: (((2,4,0) :: (((1,6,0) :: (certificate_1221_part_21_M))))))))))))))))

noncomputable def certificate_1221_part_23_M : ForbiddenMatrix := ((4,9,0) :: (((4,8,0) :: (((4,7,2) :: (((4,7,1) :: (((4,7,0) :: (((4,6,1) :: (((4,6,0) :: (((3,7,3) :: (certificate_1221_part_22_M))))))))))))))))

noncomputable def certificate_1221_part_24_M : ForbiddenMatrix := ((2,7,4) :: (((2,7,3) :: (((2,7,2) :: (((0,5,1) :: (((7,9,1) :: (((7,8,1) :: (((6,7,5) :: (((6,7,4) :: (certificate_1221_part_20_M))))))))))))))))

noncomputable def certificate_1221_part_25_M : ForbiddenMatrix := ((1,5,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((4,7,6) :: (((2,7,6) :: (((2,7,5) :: (certificate_1221_part_24_M))))))))))))))

noncomputable def certificate_1221_part_26_M : ForbiddenMatrix := ((0,8,5) :: (((0,8,4) :: (((0,8,3) :: (((0,8,2) :: (((0,6,0) :: (((4,7,6) :: (((2,7,6) :: (((2,7,5) :: (certificate_1221_part_24_M))))))))))))))))

noncomputable def certificate_1221_part_27_M : ForbiddenMatrix := ((1,8,3) :: (((1,8,2) :: (((0,9,6) :: (((0,9,5) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,8,6) :: (certificate_1221_part_26_M))))))))))))))))

noncomputable def certificate_1221_part_28_M : ForbiddenMatrix := ((1,9,6) :: (((1,9,5) :: (((1,9,4) :: (((1,9,3) :: (((1,9,2) :: (((1,8,6) :: (((1,8,5) :: (((1,8,4) :: (certificate_1221_part_27_M))))))))))))))))

noncomputable def certificate_1221_part_29_M : ForbiddenMatrix := ((3,9,3) :: (((3,9,2) :: (((3,8,6) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (((3,8,2) :: (((2,9,1) :: (certificate_1221_part_28_M))))))))))))))))

noncomputable def certificate_1221_part_30_M : ForbiddenMatrix := ((4,8,6) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,8,2) :: (((3,9,6) :: (((3,9,5) :: (((3,9,4) :: (certificate_1221_part_29_M))))))))))))))))

noncomputable def certificate_1221_part_31_M : ForbiddenMatrix := ((8,9,1) :: (((6,8,1) :: (((5,9,1) :: (((4,9,6) :: (((4,9,5) :: (((4,9,4) :: (((4,9,3) :: (((4,9,2) :: (certificate_1221_part_30_M))))))))))))))))

noncomputable def certificate_1221_part_32_M : ForbiddenMatrix := ((2,8,3) :: (((2,8,2) :: (((0,9,0) :: (((8,9,6) :: (((8,9,5) :: (((8,9,4) :: (((8,9,3) :: (((8,9,2) :: (certificate_1221_part_31_M))))))))))))))))

noncomputable def certificate_1221_part_33_M : ForbiddenMatrix := ((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((0,10,0) :: (((2,8,6) :: (((2,8,5) :: (((2,8,4) :: (certificate_1221_part_32_M))))))))))))))

noncomputable def certificate_1221_part_34_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((0,11,0) :: (((0,10,0) :: (((2,8,6) :: (((2,8,5) :: (((2,8,4) :: (certificate_1221_part_32_M))))))))))))))

noncomputable def certificate_1221_part_35_M : ForbiddenMatrix := ((0,1,3) :: (((1,4,0) :: (((0,11,0) :: (((0,10,0) :: (((2,8,6) :: (((2,8,5) :: (((2,8,4) :: (certificate_1221_part_32_M))))))))))))))

noncomputable def certificate_1221_part_36_M : ForbiddenMatrix := ((1,5,0) :: (((1,4,0) :: (((0,11,0) :: (((0,10,0) :: (((2,8,6) :: (((2,8,5) :: (((2,8,4) :: (certificate_1221_part_32_M))))))))))))))

noncomputable def certificate_1221_part_37_M : ForbiddenMatrix := ((1,9,0) :: (((1,5,0) :: (((1,4,0) :: (((0,11,0) :: (((0,10,0) :: (((2,8,6) :: (((2,8,5) :: (((2,8,4) :: (certificate_1221_part_32_M))))))))))))))))

noncomputable def certificate_1221_part_38_M : ForbiddenMatrix := ((3,6,1) :: (((3,5,1) :: (((2,5,1) :: (((1,5,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (certificate_1221_part_37_M))))))))))))))

noncomputable def certificate_1221_part_39_M : ForbiddenMatrix := ((4,6,1) :: (((3,6,2) :: (((3,6,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((2,4,0) :: (certificate_1221_part_37_M))))))))))))))

noncomputable def certificate_1221_part_40_M : ForbiddenMatrix := ((2,9,6) :: (((2,9,5) :: (((2,9,4) :: (((2,9,3) :: (((2,9,2) :: (((2,5,0) :: (((2,4,0) :: (certificate_1221_part_37_M))))))))))))))

noncomputable def certificate_1221_part_41_M : ForbiddenMatrix := ((2,9,0) :: (((2,9,6) :: (((2,9,5) :: (((2,9,4) :: (((2,9,3) :: (((2,9,2) :: (((2,5,0) :: (((2,4,0) :: (certificate_1221_part_37_M))))))))))))))))

noncomputable def certificate_1221_part_42_M : ForbiddenMatrix := ((6,9,1) :: (((6,8,6) :: (((6,8,5) :: (((6,8,4) :: (((6,8,3) :: (((6,8,2) :: (((3,5,0) :: (((3,13,1) :: (certificate_1221_part_41_M))))))))))))))))

noncomputable def certificate_1221_part_43_M : ForbiddenMatrix := ((0,15,1) :: (((0,15,0) :: (((6,9,6) :: (((6,9,5) :: (((6,9,4) :: (((6,9,3) :: (((6,9,2) :: (certificate_1221_part_42_M))))))))))))))

noncomputable def certificate_1221_part_44_M : ForbiddenMatrix := ((4,8,0) :: (((4,6,1) :: (((4,6,0) :: (((2,15,0) :: (((1,15,0) :: (((0,15,4) :: (((0,15,3) :: (((0,15,2) :: (certificate_1221_part_43_M))))))))))))))))

noncomputable def certificate_1221_part_45_M : ForbiddenMatrix := ((6,15,1) :: (((6,15,0) :: (((4,15,3) :: (((4,15,2) :: (((4,15,1) :: (((4,15,0) :: (((4,13,0) :: (((4,9,0) :: (certificate_1221_part_44_M))))))))))))))))

noncomputable def certificate_1221_part_46_M : ForbiddenMatrix := ((8,15,4) :: (((8,15,3) :: (((8,15,2) :: (((8,15,1) :: (((8,15,0) :: (((6,15,4) :: (((6,15,3) :: (((6,15,2) :: (certificate_1221_part_45_M))))))))))))))))

noncomputable def certificate_1221_part_47_M : ForbiddenMatrix := ((0,1,3) :: (((3,5,1) :: (((6,9,6) :: (((6,9,5) :: (((6,9,4) :: (((6,9,3) :: (((6,9,2) :: (certificate_1221_part_42_M))))))))))))))

noncomputable def certificate_1221_part_48_M : ForbiddenMatrix := ((3,6,0) :: (((3,5,1) :: (((6,9,6) :: (((6,9,5) :: (((6,9,4) :: (((6,9,3) :: (((6,9,2) :: (certificate_1221_part_42_M))))))))))))))

noncomputable def certificate_1221_part_49_M : ForbiddenMatrix := ((3,9,0) :: (((3,6,0) :: (((3,5,1) :: (((6,9,6) :: (((6,9,5) :: (((6,9,4) :: (((6,9,3) :: (((6,9,2) :: (certificate_1221_part_42_M))))))))))))))))

noncomputable def certificate_1221_part_50_M : ForbiddenMatrix := ((1,5,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((3,12,0) :: (((3,11,0) :: (((3,10,0) :: (certificate_1221_part_49_M))))))))))))))

noncomputable def certificate_1221_part_51_M : ForbiddenMatrix := ((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((4,6,0) :: (((3,12,0) :: (((3,11,0) :: (((3,10,0) :: (certificate_1221_part_49_M))))))))))))))

noncomputable def certificate_1221_part_52_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((4,7,0) :: (((4,6,0) :: (((3,12,0) :: (((3,11,0) :: (((3,10,0) :: (certificate_1221_part_49_M))))))))))))))

noncomputable def certificate_1221_part_53_M : ForbiddenMatrix := ((0,1,3) :: (((4,8,0) :: (((4,7,0) :: (((4,6,0) :: (((3,12,0) :: (((3,11,0) :: (((3,10,0) :: (certificate_1221_part_49_M))))))))))))))

noncomputable def certificate_1221_part_54_M : ForbiddenMatrix := ((4,9,0) :: (((4,8,0) :: (((4,7,0) :: (((4,6,0) :: (((3,12,0) :: (((3,11,0) :: (((3,10,0) :: (certificate_1221_part_49_M))))))))))))))

noncomputable def certificate_1221_part_55_M : ForbiddenMatrix := ((5,7,0) :: (((4,9,0) :: (((4,8,0) :: (((4,7,0) :: (((4,6,0) :: (((3,12,0) :: (((3,11,0) :: (((3,10,0) :: (certificate_1221_part_49_M))))))))))))))))

noncomputable def certificate_1221_part_56_M : ForbiddenMatrix := ((3,6,1) :: (((2,6,0) :: (((1,6,0) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((5,8,0) :: (certificate_1221_part_55_M))))))))))))))

noncomputable def certificate_1221_part_57_M : ForbiddenMatrix := ((0,1,3) :: (((5,8,5) :: (((5,8,4) :: (((5,8,3) :: (((5,8,2) :: (((5,8,1) :: (((5,8,0) :: (certificate_1221_part_55_M))))))))))))))

noncomputable def certificate_1221_part_58_M : ForbiddenMatrix := ((5,9,2) :: (((5,9,0) :: (((5,8,5) :: (((5,8,4) :: (((5,8,3) :: (((5,8,2) :: (((5,8,1) :: (((5,8,0) :: (certificate_1221_part_55_M))))))))))))))))

noncomputable def certificate_1225_part_1_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,1) :: (((0,3,1) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (((0,1,2) :: (((0,1,1) :: (certificate_1225_M))))))))))))))))

noncomputable def certificate_1225_part_2_M : ForbiddenMatrix := ((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,4,6) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (certificate_1225_part_1_M))))))))))))))))

noncomputable def certificate_1225_part_3_M : ForbiddenMatrix := ((0,10,2) :: (((0,10,1) :: (((0,9,6) :: (((0,9,5) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,5,6) :: (certificate_1225_part_2_M))))))))))))))))

noncomputable def certificate_1225_part_4_M : ForbiddenMatrix := ((1,4,2) :: (((1,4,1) :: (((1,3,1) :: (((1,2,1) :: (((0,10,6) :: (((0,10,5) :: (((0,10,4) :: (((0,10,3) :: (certificate_1225_part_3_M))))))))))))))))

noncomputable def certificate_1225_part_5_M : ForbiddenMatrix := ((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (certificate_1225_part_4_M))))))))))))))))

noncomputable def certificate_1225_part_6_M : ForbiddenMatrix := ((1,10,2) :: (((1,10,1) :: (((1,9,6) :: (((1,9,5) :: (((1,9,3) :: (((1,9,2) :: (((1,9,1) :: (((1,5,6) :: (certificate_1225_part_5_M))))))))))))))))

noncomputable def certificate_1225_part_7_M : ForbiddenMatrix := ((3,4,1) :: (((2,10,1) :: (((2,9,1) :: (((2,4,1) :: (((1,10,6) :: (((1,10,5) :: (((1,10,4) :: (((1,10,3) :: (certificate_1225_part_6_M))))))))))))))))

noncomputable def certificate_1225_part_8_M : ForbiddenMatrix := ((4,5,6) :: (((4,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,10,1) :: (((3,9,1) :: (certificate_1225_part_7_M))))))))))))))))

noncomputable def certificate_1225_part_9_M : ForbiddenMatrix := ((4,10,2) :: (((4,10,1) :: (((4,9,6) :: (((4,9,5) :: (((4,9,4) :: (((4,9,3) :: (((4,9,2) :: (((4,9,1) :: (certificate_1225_part_8_M))))))))))))))))

noncomputable def certificate_1225_part_10_M : ForbiddenMatrix := ((5,9,5) :: (((5,9,4) :: (((5,9,3) :: (((5,9,2) :: (((4,10,6) :: (((4,10,5) :: (((4,10,4) :: (((4,10,3) :: (certificate_1225_part_9_M))))))))))))))))

noncomputable def certificate_1225_part_11_M : ForbiddenMatrix := ((9,10,1) :: (((5,10,6) :: (((5,10,5) :: (((5,10,4) :: (((5,10,3) :: (((5,10,2) :: (((5,10,1) :: (((5,9,6) :: (certificate_1225_part_10_M))))))))))))))))

noncomputable def certificate_1225_part_12_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((9,10,6) :: (((9,10,5) :: (((9,10,4) :: (((9,10,3) :: (((9,10,2) :: (certificate_1225_part_11_M))))))))))))))

noncomputable def certificate_1225_part_13_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,2) :: (((0,4,0) :: (((9,10,6) :: (((9,10,5) :: (((9,10,4) :: (((9,10,3) :: (((9,10,2) :: (certificate_1225_part_11_M))))))))))))))))

noncomputable def certificate_1225_part_14_M : ForbiddenMatrix := ((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,3,6) :: (((0,3,5) :: (((0,3,3) :: (((0,3,2) :: (((0,2,6) :: (certificate_1225_part_13_M))))))))))))))))

noncomputable def certificate_1225_part_15_M : ForbiddenMatrix := ((1,3,2) :: (((1,2,6) :: (((1,2,5) :: (((1,2,2) :: (((0,8,1) :: (((0,7,1) :: (((0,6,6) :: (((0,6,5) :: (certificate_1225_part_14_M))))))))))))))))

noncomputable def certificate_1225_part_16_M : ForbiddenMatrix := ((1,6,6) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (((1,3,6) :: (((1,3,5) :: (((1,3,3) :: (certificate_1225_part_15_M))))))))))))))))

noncomputable def certificate_1225_part_17_M : ForbiddenMatrix := ((2,4,2) :: (((2,3,6) :: (((2,3,5) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,8,1) :: (((1,7,1) :: (certificate_1225_part_16_M))))))))))))))))

noncomputable def certificate_1225_part_18_M : ForbiddenMatrix := ((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (((2,6,2) :: (((2,4,6) :: (((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (certificate_1225_part_17_M))))))))))))))))

noncomputable def certificate_1225_part_19_M : ForbiddenMatrix := ((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((2,8,1) :: (((2,7,1) :: (((2,6,6) :: (certificate_1225_part_18_M))))))))))))))))

noncomputable def certificate_1225_part_20_M : ForbiddenMatrix := ((4,6,5) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((3,6,6) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (certificate_1225_part_19_M))))))))))))))))

noncomputable def certificate_1225_part_21_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((6,7,1) :: (((5,6,1) :: (((4,6,6) :: (certificate_1225_part_20_M))))))))))))))

noncomputable def certificate_1225_part_22_M : ForbiddenMatrix := ((2,6,1) :: (((2,3,4) :: (((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,6,1) :: (((0,3,4) :: (certificate_1225_part_21_M))))))))))))))))

noncomputable def certificate_1225_part_23_M : ForbiddenMatrix := ((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,5,0) :: (((6,7,1) :: (((5,6,1) :: (((4,6,6) :: (certificate_1225_part_20_M))))))))))))))))

noncomputable def certificate_1225_part_24_M : ForbiddenMatrix := ((4,7,4) :: (((4,7,3) :: (((1,7,6) :: (((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,7,2) :: (((0,7,6) :: (certificate_1225_part_23_M))))))))))))))))

noncomputable def certificate_1225_part_25_M : ForbiddenMatrix := ((6,9,4) :: (((6,9,3) :: (((6,9,2) :: (((6,7,5) :: (((6,7,4) :: (((6,7,3) :: (((6,7,2) :: (((4,7,5) :: (certificate_1225_part_24_M))))))))))))))))

noncomputable def certificate_1225_part_26_M : ForbiddenMatrix := ((7,9,6) :: (((7,9,5) :: (((7,9,4) :: (((7,9,3) :: (((7,9,2) :: (((7,9,1) :: (((7,8,1) :: (((6,9,5) :: (certificate_1225_part_25_M))))))))))))))))

noncomputable def certificate_1225_part_27_M : ForbiddenMatrix := ((1,4,0) :: (((0,9,4) :: (((0,6,1) :: (((0,6,0) :: (((0,1,4) :: (((0,1,3) :: (((8,9,1) :: (certificate_1225_part_26_M))))))))))))))

noncomputable def certificate_1225_part_28_M : ForbiddenMatrix := ((4,6,0) :: (((3,7,1) :: (((3,6,0) :: (((2,6,0) :: (((2,4,0) :: (((1,9,4) :: (((1,6,1) :: (((1,6,0) :: (certificate_1225_part_27_M))))))))))))))))

noncomputable def certificate_1225_part_29_M : ForbiddenMatrix := ((6,9,1) :: (((6,9,0) :: (((4,9,0) :: (((4,8,0) :: (((4,7,2) :: (((4,7,1) :: (((4,7,0) :: (((4,6,1) :: (certificate_1225_part_28_M))))))))))))))))

noncomputable def certificate_1225_part_30_M : ForbiddenMatrix := ((3,7,4) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,7,3) :: (((2,7,2) :: (((0,5,1) :: (((8,9,1) :: (certificate_1225_part_26_M))))))))))))))))

noncomputable def certificate_1225_part_31_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((4,7,6) :: (((3,7,6) :: (((3,7,5) :: (certificate_1225_part_30_M))))))))))))))

noncomputable def certificate_1225_part_32_M : ForbiddenMatrix := ((3,7,1) :: (((2,5,1) :: (((2,3,4) :: (((1,5,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (certificate_1225_part_31_M))))))))))))))))

noncomputable def certificate_1225_part_33_M : ForbiddenMatrix := ((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((0,6,0) :: (((4,7,6) :: (((3,7,6) :: (((3,7,5) :: (certificate_1225_part_30_M))))))))))))))

noncomputable def certificate_1225_part_34_M : ForbiddenMatrix := ((1,9,4) :: (((1,7,0) :: (((1,5,1) :: (((1,5,0) :: (((0,9,4) :: (((0,7,0) :: (((0,1,4) :: (((0,1,3) :: (certificate_1225_part_33_M))))))))))))))))

noncomputable def certificate_1225_part_35_M : ForbiddenMatrix := ((5,7,0) :: (((4,8,1) :: (((4,7,2) :: (((4,7,1) :: (((4,7,0) :: (((3,7,0) :: (((2,7,0) :: (((2,5,0) :: (certificate_1225_part_34_M))))))))))))))))

noncomputable def certificate_1225_part_36_M : ForbiddenMatrix := ((0,6,1) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((0,6,0) :: (((4,7,6) :: (((3,7,6) :: (((3,7,5) :: (certificate_1225_part_30_M))))))))))))))))

noncomputable def certificate_1225_part_37_M : ForbiddenMatrix := ((3,10,4) :: (((3,10,3) :: (((3,10,2) :: (((3,9,6) :: (((3,9,5) :: (((3,9,4) :: (((3,9,3) :: (((3,9,2) :: (certificate_1225_part_36_M))))))))))))))))

noncomputable def certificate_1225_part_38_M : ForbiddenMatrix := ((1,3,4) :: (((0,9,4) :: (((0,3,4) :: (((0,1,4) :: (((0,1,3) :: (((3,10,6) :: (((3,10,5) :: (certificate_1225_part_37_M))))))))))))))

noncomputable def certificate_1225_part_39_M : ForbiddenMatrix := ((0,11,6) :: (((0,11,5) :: (((0,11,4) :: (((0,11,3) :: (((0,11,2) :: (((0,7,0) :: (((3,10,6) :: (((3,10,5) :: (certificate_1225_part_37_M))))))))))))))))

noncomputable def certificate_1225_part_40_M : ForbiddenMatrix := ((3,11,4) :: (((3,11,3) :: (((3,11,2) :: (((1,11,6) :: (((1,11,5) :: (((1,11,4) :: (((1,11,3) :: (((1,11,2) :: (certificate_1225_part_39_M))))))))))))))))

noncomputable def certificate_1225_part_41_M : ForbiddenMatrix := ((4,11,6) :: (((4,11,5) :: (((4,11,4) :: (((4,11,3) :: (((4,11,2) :: (((4,11,1) :: (((3,11,6) :: (((3,11,5) :: (certificate_1225_part_40_M))))))))))))))))

noncomputable def certificate_1225_part_42_M : ForbiddenMatrix := ((10,11,6) :: (((10,11,5) :: (((10,11,4) :: (((10,11,3) :: (((10,11,2) :: (((10,11,1) :: (((7,11,1) :: (certificate_1225_part_41_M))))))))))))))

noncomputable def certificate_1225_part_43_M : ForbiddenMatrix := ((0,10,0) :: (((10,11,6) :: (((10,11,5) :: (((10,11,4) :: (((10,11,3) :: (((10,11,2) :: (((10,11,1) :: (((7,11,1) :: (certificate_1225_part_41_M))))))))))))))))

noncomputable def certificate_1225_part_44_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((2,9,6) :: (((2,9,5) :: (((2,9,3) :: (((2,9,2) :: (certificate_1225_part_43_M))))))))))))))

noncomputable def certificate_1225_part_45_M : ForbiddenMatrix := ((2,3,4) :: (((1,9,4) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (certificate_1225_part_44_M))))))))))))))))

noncomputable def certificate_1225_part_46_M : ForbiddenMatrix := ((0,12,4) :: (((0,12,3) :: (((0,12,2) :: (((0,11,0) :: (((2,9,6) :: (((2,9,5) :: (((2,9,3) :: (((2,9,2) :: (certificate_1225_part_43_M))))))))))))))))

noncomputable def certificate_1225_part_47_M : ForbiddenMatrix := ((3,12,4) :: (((3,12,3) :: (((3,12,2) :: (((1,12,5) :: (((1,12,4) :: (((1,12,3) :: (((1,12,2) :: (((0,12,5) :: (certificate_1225_part_46_M))))))))))))))))

noncomputable def certificate_1225_part_48_M : ForbiddenMatrix := ((10,12,2) :: (((4,12,5) :: (((4,12,4) :: (((4,12,3) :: (((4,12,2) :: (((4,12,1) :: (((3,13,1) :: (((3,12,5) :: (certificate_1225_part_47_M))))))))))))))))

noncomputable def certificate_1225_part_49_M : ForbiddenMatrix := ((0,12,1) :: (((0,12,0) :: (((0,3,4) :: (((0,1,4) :: (((0,1,3) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))

noncomputable def certificate_1225_part_50_M : ForbiddenMatrix := ((3,12,0) :: (((3,10,0) :: (((2,12,0) :: (((2,10,0) :: (((1,12,1) :: (((1,12,0) :: (((1,10,0) :: (((1,3,4) :: (certificate_1225_part_49_M))))))))))))))))

noncomputable def certificate_1225_part_51_M : ForbiddenMatrix := ((1,5,1) :: (((0,9,4) :: (((0,1,4) :: (((0,1,3) :: (((0,11,1) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))

noncomputable def certificate_1225_part_52_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((1,4,0) :: (((0,11,1) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))

noncomputable def certificate_1225_part_53_M : ForbiddenMatrix := ((2,6,1) :: (((2,3,4) :: (((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (((0,2,4) :: (certificate_1225_part_52_M))))))))))))))))

noncomputable def certificate_1225_part_54_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((1,5,0) :: (((1,4,0) :: (((0,11,1) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))

noncomputable def certificate_1225_part_55_M : ForbiddenMatrix := ((2,3,4) :: (((1,5,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (certificate_1225_part_54_M))))))))))))))))

noncomputable def certificate_1225_part_56_M : ForbiddenMatrix := ((0,1,3) :: (((1,6,0) :: (((1,5,0) :: (((1,4,0) :: (((0,11,1) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))

noncomputable def certificate_1225_part_57_M : ForbiddenMatrix := ((1,10,0) :: (((1,6,0) :: (((1,5,0) :: (((1,4,0) :: (((0,11,1) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))

noncomputable def certificate_1225_part_58_M : ForbiddenMatrix := ((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (certificate_1225_part_57_M))))))))))))))))

noncomputable def certificate_1225_part_59_M : ForbiddenMatrix := ((1,11,0) :: (((1,10,0) :: (((1,6,0) :: (((1,5,0) :: (((1,4,0) :: (((0,11,1) :: (((10,12,4) :: (((10,12,3) :: (certificate_1225_part_48_M))))))))))))))))

noncomputable def certificate_1225_part_60_M : ForbiddenMatrix := ((2,10,4) :: (((2,10,3) :: (((2,10,2) :: (((2,5,6) :: (((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (((2,5,2) :: (certificate_1225_part_59_M))))))))))))))))

noncomputable def certificate_1225_part_61_M : ForbiddenMatrix := ((2,5,1) :: (((1,5,1) :: (((0,9,4) :: (((0,2,4) :: (((0,2,3) :: (((2,10,6) :: (((2,10,5) :: (certificate_1225_part_60_M))))))))))))))

noncomputable def certificate_1225_part_62_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((2,4,0) :: (((2,10,6) :: (((2,10,5) :: (certificate_1225_part_60_M))))))))))))))

noncomputable def certificate_1225_part_63_M : ForbiddenMatrix := ((3,6,1) :: (((2,6,1) :: (((2,3,4) :: (((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (certificate_1225_part_62_M))))))))))))))))

noncomputable def certificate_1225_part_64_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((2,5,0) :: (((2,4,0) :: (((2,10,6) :: (((2,10,5) :: (certificate_1225_part_60_M))))))))))))))

noncomputable def certificate_1225_part_65_M : ForbiddenMatrix := ((2,5,1) :: (((2,3,4) :: (((1,5,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (((0,2,4) :: (certificate_1225_part_64_M))))))))))))))))

noncomputable def certificate_1225_part_66_M : ForbiddenMatrix := ((2,11,4) :: (((2,11,3) :: (((2,11,2) :: (((2,6,0) :: (((2,5,0) :: (((2,4,0) :: (((2,10,6) :: (((2,10,5) :: (certificate_1225_part_60_M))))))))))))))))

noncomputable def certificate_1225_part_67_M : ForbiddenMatrix := ((2,3,4) :: (((1,11,1) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((2,11,6) :: (((2,11,5) :: (certificate_1225_part_66_M))))))))))))))

noncomputable def certificate_1225_part_68_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((2,10,0) :: (((2,11,6) :: (((2,11,5) :: (certificate_1225_part_66_M))))))))))))))

noncomputable def certificate_1225_part_69_M : ForbiddenMatrix := ((2,9,4) :: (((2,3,4) :: (((1,9,4) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (certificate_1225_part_68_M))))))))))))))))

noncomputable def certificate_1225_part_70_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((3,5,0) :: (((2,11,0) :: (((2,10,0) :: (((2,11,6) :: (((2,11,5) :: (certificate_1225_part_66_M))))))))))))))

noncomputable def certificate_1225_part_71_M : ForbiddenMatrix := ((1,5,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (certificate_1225_part_70_M))))))))))))))))

noncomputable def certificate_1225_part_72_M : ForbiddenMatrix := ((0,1,3) :: (((3,6,0) :: (((3,5,0) :: (((2,11,0) :: (((2,10,0) :: (((2,11,6) :: (((2,11,5) :: (certificate_1225_part_66_M))))))))))))))

noncomputable def certificate_1225_part_73_M : ForbiddenMatrix := ((3,10,0) :: (((3,6,0) :: (((3,5,0) :: (((2,11,0) :: (((2,10,0) :: (((2,11,6) :: (((2,11,5) :: (certificate_1225_part_66_M))))))))))))))

noncomputable def certificate_1225_part_74_M : ForbiddenMatrix := ((1,9,4) :: (((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (certificate_1225_part_73_M))))))))))))))))

noncomputable def certificate_1225_part_75_M : ForbiddenMatrix := ((3,11,0) :: (((3,10,0) :: (((3,6,0) :: (((3,5,0) :: (((2,11,0) :: (((2,10,0) :: (((2,11,6) :: (((2,11,5) :: (certificate_1225_part_66_M))))))))))))))))

noncomputable def certificate_1225_part_76_M : ForbiddenMatrix := ((0,9,4) :: (((0,3,4) :: (((3,5,6) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_1225_part_75_M))))))))))))))

noncomputable def certificate_1225_part_77_M : ForbiddenMatrix := ((0,8,3) :: (((0,8,2) :: (((4,6,0) :: (((3,5,6) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_1225_part_75_M))))))))))))))))

noncomputable def certificate_1225_part_78_M : ForbiddenMatrix := ((7,10,5) :: (((7,10,4) :: (((7,10,3) :: (((7,10,2) :: (((7,10,1) :: (((7,8,3) :: (((7,8,2) :: (((5,7,5) :: (certificate_1225_part_77_M))))))))))))))))

noncomputable def certificate_1225_part_79_M : ForbiddenMatrix := ((0,15,2) :: (((0,15,1) :: (((0,15,0) :: (((8,10,3) :: (((8,10,2) :: (((8,10,1) :: (((7,10,6) :: (certificate_1225_part_78_M))))))))))))))

noncomputable def certificate_1225_part_80_M : ForbiddenMatrix := ((5,7,1) :: (((5,7,0) :: (((3,15,0) :: (((2,15,0) :: (((1,15,0) :: (((0,15,5) :: (((0,15,4) :: (((0,15,3) :: (certificate_1225_part_79_M))))))))))))))))

noncomputable def certificate_1225_part_81_M : ForbiddenMatrix := ((5,15,3) :: (((5,15,2) :: (((5,15,1) :: (((5,15,0) :: (((5,10,0) :: (((5,9,0) :: (((5,8,2) :: (((5,8,1) :: (certificate_1225_part_80_M))))))))))))))))

noncomputable def certificate_1225_part_82_M : ForbiddenMatrix := ((8,15,1) :: (((7,15,5) :: (((7,15,4) :: (((7,15,3) :: (((7,15,2) :: (((7,15,1) :: (((7,15,0) :: (((5,15,4) :: (certificate_1225_part_81_M))))))))))))))))

noncomputable def certificate_1225_part_83_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((4,6,1) :: (((8,10,3) :: (((8,10,2) :: (((8,10,1) :: (((7,10,6) :: (certificate_1225_part_78_M))))))))))))))

noncomputable def certificate_1225_part_84_M : ForbiddenMatrix := ((1,5,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (certificate_1225_part_83_M))))))))))))))))

noncomputable def certificate_1225_part_85_M : ForbiddenMatrix := ((5,9,1) :: (((3,6,1) :: (((2,9,4) :: (((2,6,1) :: (((2,5,1) :: (((2,3,4) :: (((1,9,4) :: (((1,6,1) :: (certificate_1225_part_84_M))))))))))))))))

noncomputable def certificate_1225_part_86_M : ForbiddenMatrix := ((0,1,3) :: (((4,7,0) :: (((4,6,1) :: (((8,10,3) :: (((8,10,2) :: (((8,10,1) :: (((7,10,6) :: (certificate_1225_part_78_M))))))))))))))

noncomputable def certificate_1225_part_87_M : ForbiddenMatrix := ((1,5,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (certificate_1225_part_86_M))))))))))))))))

noncomputable def certificate_1225_part_88_M : ForbiddenMatrix := ((4,9,0) :: (((4,7,0) :: (((4,6,1) :: (((8,10,3) :: (((8,10,2) :: (((8,10,1) :: (((7,10,6) :: (certificate_1225_part_78_M))))))))))))))

noncomputable def certificate_1225_part_89_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (certificate_1225_part_88_M))))))))))))))))

noncomputable def certificate_1225_part_90_M : ForbiddenMatrix := ((4,10,0) :: (((4,9,0) :: (((4,7,0) :: (((4,6,1) :: (((8,10,3) :: (((8,10,2) :: (((8,10,1) :: (((7,10,6) :: (certificate_1225_part_78_M))))))))))))))))

noncomputable def certificate_1225_part_91_M : ForbiddenMatrix := ((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (certificate_1225_part_90_M))))))))))))))

noncomputable def certificate_1225_part_92_M : ForbiddenMatrix := ((0,9,4) :: (((0,3,4) :: (((0,1,3) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,11,0) :: (certificate_1225_part_90_M))))))))))))))

noncomputable def certificate_1225_part_93_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((5,7,0) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,11,0) :: (certificate_1225_part_90_M))))))))))))))

noncomputable def certificate_1225_part_94_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (certificate_1225_part_93_M))))))))))))))))

noncomputable def certificate_1225_part_95_M : ForbiddenMatrix := ((0,1,3) :: (((5,8,0) :: (((5,7,0) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,11,0) :: (certificate_1225_part_90_M))))))))))))))

noncomputable def certificate_1225_part_96_M : ForbiddenMatrix := ((1,6,1) :: (((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (certificate_1225_part_95_M))))))))))))))))

noncomputable def certificate_1225_part_97_M : ForbiddenMatrix := ((5,10,0) :: (((5,8,0) :: (((5,7,0) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,11,0) :: (certificate_1225_part_90_M))))))))))))))

noncomputable def certificate_1225_part_98_M : ForbiddenMatrix := ((1,2,4) :: (((1,2,3) :: (((0,9,4) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (certificate_1225_part_97_M))))))))))))))))

noncomputable def certificate_1225_part_99_M : ForbiddenMatrix := ((5,11,0) :: (((5,10,0) :: (((5,8,0) :: (((5,7,0) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,11,0) :: (certificate_1225_part_90_M))))))))))))))))

noncomputable def certificate_1225_part_100_M : ForbiddenMatrix := ((6,12,2) :: (((6,10,6) :: (((6,10,5) :: (((6,10,4) :: (((6,10,3) :: (((6,10,2) :: (((6,10,1) :: (((4,12,6) :: (certificate_1225_part_99_M))))))))))))))))

noncomputable def certificate_1225_part_101_M : ForbiddenMatrix := ((0,12,1) :: (((10,12,6) :: (((10,12,5) :: (((6,12,6) :: (((6,12,5) :: (((6,12,4) :: (((6,12,3) :: (certificate_1225_part_100_M))))))))))))))

noncomputable def certificate_1225_part_102_M : ForbiddenMatrix := ((2,12,1) :: (((2,6,1) :: (((1,15,1) :: (((1,12,1) :: (((1,6,1) :: (((0,15,3) :: (((0,15,2) :: (((0,15,1) :: (certificate_1225_part_101_M))))))))))))))))

noncomputable def certificate_1225_part_103_M : ForbiddenMatrix := ((4,15,2) :: (((4,15,1) :: (((4,15,0) :: (((4,12,0) :: (((3,15,1) :: (((3,12,1) :: (((3,6,1) :: (((2,15,1) :: (certificate_1225_part_102_M))))))))))))))))

noncomputable def certificate_1225_part_104_M : ForbiddenMatrix := ((6,15,2) :: (((6,15,1) :: (((6,12,1) :: (((6,10,0) :: (((4,15,6) :: (((4,15,5) :: (((4,15,4) :: (((4,15,3) :: (certificate_1225_part_103_M))))))))))))))))

noncomputable def certificate_1225_part_105_M : ForbiddenMatrix := ((10,15,3) :: (((10,15,2) :: (((10,15,1) :: (((10,12,1) :: (((6,15,6) :: (((6,15,5) :: (((6,15,4) :: (((6,15,3) :: (certificate_1225_part_104_M))))))))))))))))

noncomputable def certificate_1225_part_106_M : ForbiddenMatrix := ((12,15,5) :: (((12,15,4) :: (((12,15,3) :: (((12,15,2) :: (((12,15,1) :: (((10,15,6) :: (((10,15,5) :: (((10,15,4) :: (certificate_1225_part_105_M))))))))))))))))

noncomputable def certificate_1225_part_107_M : ForbiddenMatrix := ((5,11,2) :: (((5,11,1) :: (((10,12,6) :: (((10,12,5) :: (((6,12,6) :: (((6,12,5) :: (((6,12,4) :: (((6,12,3) :: (certificate_1225_part_100_M))))))))))))))))

noncomputable def certificate_1225_part_108_M : ForbiddenMatrix := ((5,12,5) :: (((5,12,4) :: (((5,12,3) :: (((5,12,2) :: (((5,7,6) :: (((6,8,0) :: (((5,11,4) :: (((5,11,3) :: (certificate_1225_part_107_M))))))))))))))))

noncomputable def certificate_1225_part_109_M : ForbiddenMatrix := ((7,12,6) :: (((7,12,5) :: (((7,12,4) :: (((7,12,3) :: (((7,12,2) :: (((7,12,1) :: (((5,12,6) :: (certificate_1225_part_108_M))))))))))))))

noncomputable def certificate_1225_part_110_M : ForbiddenMatrix := ((2,5,1) :: (((1,15,1) :: (((1,12,1) :: (((1,5,1) :: (((0,15,3) :: (((0,15,2) :: (((0,15,1) :: (((0,12,1) :: (certificate_1225_part_109_M))))))))))))))))

noncomputable def certificate_1225_part_111_M : ForbiddenMatrix := ((5,12,1) :: (((5,12,0) :: (((5,7,1) :: (((3,15,1) :: (((3,12,1) :: (((3,7,1) :: (((2,15,1) :: (((2,12,1) :: (certificate_1225_part_110_M))))))))))))))))

noncomputable def certificate_1225_part_112_M : ForbiddenMatrix := ((7,10,0) :: (((5,15,6) :: (((5,15,5) :: (((5,15,4) :: (((5,15,3) :: (((5,15,2) :: (((5,15,1) :: (((5,15,0) :: (certificate_1225_part_111_M))))))))))))))))

noncomputable def certificate_1225_part_113_M : ForbiddenMatrix := ((10,15,1) :: (((10,12,1) :: (((7,15,6) :: (((7,15,5) :: (((7,15,4) :: (((7,15,3) :: (((7,15,2) :: (((7,15,1) :: (certificate_1225_part_112_M))))))))))))))))

noncomputable def certificate_1225_part_114_M : ForbiddenMatrix := ((12,15,3) :: (((12,15,2) :: (((12,15,1) :: (((10,15,6) :: (((10,15,5) :: (((10,15,4) :: (((10,15,3) :: (((10,15,2) :: (certificate_1225_part_113_M))))))))))))))))

noncomputable def certificate_1225_part_115_M : ForbiddenMatrix := ((6,11,1) :: (((7,12,6) :: (((7,12,5) :: (((7,12,4) :: (((7,12,3) :: (((7,12,2) :: (((7,12,1) :: (((5,12,6) :: (certificate_1225_part_108_M))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates040
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1260_part_1 : FiniteCertificate := .forbid 2 3 5 (.system [[0],[1],[2,14,15,16,17,18,3,4,5,6,7],[8],[13]]) (.forbid 2 3 6 (.system [[0],[1],[2,14,15,16,17,18,19,3,4],[7],[8],[13]]) (.forbid 2 5 1 (.system [[0],[1],[2,14,5,6,7],[4],[8,9,10,11,12,13]]) (.forbid 2 5 2 (.system [[0],[1],[2,14,15,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 5 3 (.system [[0],[1],[2,14,15,16,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 5 4 (.system [[0],[1],[2,14,15,16,17,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 5 5 (.system [[0],[1],[2,14,15,16,17,18,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 5 6 (.system [[0],[1],[2,14,15,16,17,18,19,5,4],[7],[8],[13]]) (.forbid 2 6 1 (.system [[0],[1],[2,14,6,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 6 2 (.system [[0],[1],[2,14,15,6,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 6 3 (.system [[0],[1],[2,14,15,16,6,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 6 4 (.system [[0],[1],[2,14,15,16,17,6,5,4],[7],[8,9,10,11,12,13]]) (.forbid 2 6 5 (.system [[0],[1],[2,14,15,16,17,18,6,5,4],[7],[8],[13]]) (.forbid 2 6 6 (.system [[0],[1],[2,14,15,16,17,18,19,6,5,4],[7],[8],[13]]) (.forbid 2 8 1 (.system [[0],[1],[7,6,5,4,3,2,14,8,9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0],[1],[2,3,14,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 3 5 1 (.system [[0],[1],[2,3,14,5,4],[7],[8,9,10,11,12,13]]) (.forbid 3 5 2 (.system [[0],[1],[2,3,14,15,5,4],[7],[8,9,10,11,12,13]]) (.forbid 3 5 3 (.system [[0],[1],[2,3,14,15,16,5,4],[7],[8,9,10,11,12,13]]) (.forbid 3 5 4 (.system [[0],[1],[2,3,14,15,16,17,5,4],[7],[8,9,10,11,12,13]]) (certificate_1260_part_0))))))))))))))))))))

noncomputable def certificate_1260_part_2 : FiniteCertificate := .forbid 1 3 4 (.system [[0],[1,14,15,16,17,3,2],[4,5,6,7],[8],[13]]) (.forbid 1 3 5 (.system [[0],[1,14,15,16,17,18,3,2],[4,5,6,7],[8],[13]]) (.forbid 1 3 6 (.system [[0],[1,14,15,16,17,18,19,3,2],[4],[7],[8],[13]]) (.forbid 1 5 1 (.system [[0],[1,14,5,6,7],[2],[4],[8,9,10,11,12,13]]) (.forbid 1 5 2 (.system [[0],[1,14,15,5,4],[2],[7],[8,9,10,11,12,13]]) (.forbid 1 5 3 (.system [[0],[1,14,15,16,5,4],[2],[7],[8,9,10,11,12,13]]) (.forbid 1 5 4 (.system [[0],[1,14,15,16,17,5,4],[2],[7],[8,9,10,11,12,13]]) (.forbid 1 5 5 (.system [[0],[1,14,15,16,17,18,5,4,3,2],[7],[8],[13]]) (.forbid 1 5 6 (.system [[0],[1,14,15,16,17,18,19,5,4],[2],[7],[8],[13]]) (.forbid 1 6 1 (.system [[0],[1,14,6,5,4],[2],[7],[8,9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0],[1,14,15,6,5,4],[2],[7],[8,9,10,11,12,13]]) (.forbid 1 6 3 (.system [[0],[1,14,15,16,6,5,4],[2],[7],[8,9,10,11,12,13]]) (.forbid 1 6 4 (.system [[0],[1,14,15,16,17,6,5,4,3,2],[7],[8],[13]]) (.forbid 1 6 5 (.system [[0],[1,14,15,16,17,18,6,5,4],[2],[7],[8],[13]]) (.forbid 1 6 6 (.system [[0],[1,14,15,16,17,18,19,6,5,4],[2],[7],[8],[13]]) (.forbid 1 7 1 (.system [[0],[1,14,7,6,5,4,3,2],[8,9,10,11,12,13]]) (.forbid 2 3 1 (.system [[0],[1],[2,14,3,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 2 3 2 (.system [[0],[1],[2,14,15,3,4],[7],[8,9,10,11,12,13]]) (.forbid 2 3 3 (.system [[0],[1],[2,14,15,16,3,4],[7],[8,9,10,11,12,13]]) (.forbid 2 3 4 (.system [[0],[1],[2,14,15,16,17,3,4,5,6,7],[8],[13]]) (certificate_1260_part_1))))))))))))))))))))

noncomputable def certificate_1260_part_3 : FiniteCertificate := .forbid 0 5 3 (.system [[0,14,15,16,5,4],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5,4],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,4,3,2],[1],[7],[8],[13]]) (.forbid 0 5 6 (.system [[0,14,15,16,17,18,19,5,4],[1],[2],[7],[8],[13]]) (.forbid 0 6 1 (.system [[0,14,6,5,4],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 6 2 (.system [[0,14,15,6,5,4],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 6 3 (.system [[0,14,15,16,6,5,4],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5,4,3,2],[1],[7],[8],[13]]) (.forbid 0 6 5 (.system [[0,14,15,16,17,18,6,5,4],[1],[2],[7],[8],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5,4],[1],[2],[7],[8],[13]]) (.forbid 0 7 1 (.system [[0,14,7,6,5,4,3,2],[1],[8,9,10,11,12,13]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2],[4,5,6,7],[8,9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2],[4],[7],[8,9,10,11,12,13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2],[4],[7],[8,9,10,11,12,13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2],[4,5,6,7],[8],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2,3,4],[7],[8],[13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,2],[4,5,6,7],[8,9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0],[1,14,15,3,2],[4],[7],[8,9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0],[1,14,15,16,3,2],[4],[7],[8,9,10,11,12,13]]) (certificate_1260_part_2))))))))))))))))))))

noncomputable def certificate_1260 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2,3,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[2],[4,5,6,7],[8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[2],[4],[7],[8,9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[2],[4],[7],[8,9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[2],[4,5,6,7],[8],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1],[2,3,4],[7],[8],[13]]) (.forbid 0 2 1 (.system [[0,14,2,3,4,5,6,7],[1],[8,9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2],[1],[4,5,6,7],[8,9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2],[1],[4],[7],[8,9,10,11,12,13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2],[1],[4],[7],[8,9,10,11,12,13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2],[1],[4,5,6,7],[8],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2,3,4],[1],[7],[8],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[1],[4,5,6,7],[8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[1],[4],[7],[8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[1],[4],[7],[8,9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[1],[4,5,6,7],[8],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[1],[4,5,6,7],[8],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[1],[4],[7],[8],[13]]) (.forbid 0 5 1 (.system [[0,14,5,6,7],[1],[2],[4],[8,9,10,11,12,13]]) (.forbid 0 5 2 (.system [[0,14,15,5,4],[1],[2],[7],[8,9,10,11,12,13]]) (certificate_1260_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates041
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1286 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1],[2,3,4,5,6,7,8,9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1],[2,3,4,5],[7],[9,10,11,12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1],[2,3,4,5,6,7],[9],[12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1],[2,3,4,5],[7],[9],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1],[2,3,4,5],[7],[9],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1],[2],[5],[7],[9],[12]]) (.forbid 0 2 1 (.system [[0,13,2,3,4,5,6,7,8,9,10,11,12],[1]]) (.forbid 0 2 2 (.system [[0,13,14,2,3,4,5],[1],[7],[9,10,11,12]]) (.forbid 0 2 3 (.system [[0,13,14,15,2,3,4,5,6,7],[1],[9],[12]]) (.forbid 0 2 4 (.system [[0,13,14,15,16,2,3,4,5],[1],[7],[9],[12]]) (.forbid 0 2 5 (.system [[0,13,14,15,16,17,2,3,4,5],[1],[7],[9],[12]]) (.forbid 0 2 6 (.system [[0,13,14,15,16,17,18,2],[1],[5],[7],[9],[12]]) (.forbid 0 3 1 (.system [[0,13,3,4,5,6,7],[1],[2],[9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3,2],[1],[5,6,7],[9,10,11,12]]) (.forbid 0 3 3 (.system [[0,13,14,15,3,2],[1],[5],[7],[9,10,11,12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3,2],[1],[5,6,7],[9],[12]]) (.forbid 0 3 5 (.system [[0,13,14,15,16,17,3,2],[1],[5],[7],[9],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3,2],[1],[5],[7],[9],[12]]) (.forbid 0 6 1 (.system [[0,13,6,5,4,3,2],[1],[7],[9,10,11,12]]) (.forbid 0 6 2 (.system [[0,13,14,6,5,4,3,2],[1],[7,8,9],[12]]) (certificate_1286_part_3))))))))))))))))))))

noncomputable def certificate_1311_part_2 : FiniteCertificate := .forbid 1 4 4 (.system [[0],[1,14,15,16,17,4],[3],[6],[9,10,11,12,13]]) (.forbid 1 4 5 (.system [[0],[1,14,15,16,17,18,4],[3],[6,7,8,9],[13]]) (.forbid 1 4 6 (.system [[0],[3,2,1,14,15,16,17,18,19,4],[6],[9],[13]]) (.forbid 1 5 1 (.system [[0],[1,14,5,4],[3],[6,7,8,9,10,11,12,13]]) (.forbid 1 5 2 (.system [[0],[3,2,1,14,15,5,4],[6],[9,10,11,12,13]]) (.forbid 1 5 3 (.system [[0],[1,14,15,16,5,4],[3],[6],[9,10,11,12,13]]) (.forbid 1 5 4 (.system [[0],[1,14,15,16,17,5,4],[3],[6,7,8,9],[13]]) (.forbid 1 5 5 (.system [[0],[3,2,1,14,15,16,17,18,5,4],[6],[9],[13]]) (.forbid 1 5 6 (.system [[0],[1,14,15,16,17,18,19,5,4],[3],[6],[9],[13]]) (.forbid 1 7 1 (.system [[0],[3,2,1,14,7,8,9,10,11,12,13],[4],[6]]) (.forbid 1 7 2 (.system [[0],[3,2,1,14,15,7,6],[4],[9,10,11,12,13]]) (.forbid 1 7 3 (.system [[0],[1,14,15,16,7,6],[3],[4],[9,10,11,12,13]]) (.forbid 1 7 4 (.system [[0],[1,14,15,16,17,7,6],[3],[4],[9,10,11,12,13]]) (.forbid 1 7 5 (.system [[0],[3,2,1,14,15,16,17,18,7,6],[4],[9],[13]]) (.forbid 1 7 6 (.system [[0],[1,14,15,16,17,18,19,7,6],[3],[4],[9],[13]]) (.forbid 1 8 1 (.system [[0],[3,2,1,14,8,7,6],[4],[9,10,11,12,13]]) (.forbid 2 3 1 (.system [[0],[1,2,14,3],[4],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[1,2,14,4],[3],[6,7,8,9,10,11,12,13]]) (.forbid 2 4 2 (.system [[0],[1,2,14,15,4,5,6],[3],[9,10,11,12,13]]) (.forbid 2 4 3 (.system [[0],[1,2,14,15,16,4],[3],[6],[9,10,11,12,13]]) (certificate_1311_part_1))))))))))))))))))))

noncomputable def certificate_1311_part_3 : FiniteCertificate := .forbid 0 5 2 (.system [[0,14,15,5,4],[1,2,3],[6],[9,10,11,12,13]]) (.forbid 0 5 3 (.system [[0,14,15,16,5,4],[1],[3],[6],[9,10,11,12,13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5,4],[1],[3],[6,7,8,9],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,4],[1,2,3],[6],[9],[13]]) (.forbid 0 5 6 (.system [[0,14,15,16,17,18,19,5,4],[1],[3],[6],[9],[13]]) (.forbid 0 7 1 (.system [[0,14,7,8,9,10,11,12,13],[1,2,3],[4],[6]]) (.forbid 0 7 2 (.system [[0,14,15,7,6],[1,2,3],[4],[9,10,11,12,13]]) (.forbid 0 7 3 (.system [[0,14,15,16,7,6],[1],[3],[4],[9,10,11,12,13]]) (.forbid 0 7 4 (.system [[0,14,15,16,17,7,6],[1],[3],[4],[9,10,11,12,13]]) (.forbid 0 7 5 (.system [[0,14,15,16,17,18,7,6],[1,2,3],[4],[9],[13]]) (.forbid 0 7 6 (.system [[0,14,15,16,17,18,19,7,6],[1],[3],[4],[9],[13]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3],[4],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2,3],[4,5,6],[9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2,3],[4],[6],[9,10,11,12,13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2,3],[4],[6,7,8,9],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2,3],[4,5,6],[9],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2,3],[4],[6],[9],[13]]) (.forbid 1 4 1 (.system [[0],[3,2,1,14,4,5,6,7,8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4],[3],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0],[3,2,1,14,15,16,4],[6],[9,10,11,12,13]]) (certificate_1311_part_2))))))))))))))))))))

noncomputable def certificate_1311 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[3],[4],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2,3],[4],[6],[9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[3],[4],[6],[9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[3],[4],[6,7,8,9],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2,3],[4],[6],[9],[13]]) (.forbid 0 2 1 (.system [[0,14,2,1],[3],[4],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2,1],[3],[4,5,6],[9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2,1],[3],[4],[6],[9,10,11,12,13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2,1],[3],[4],[6,7,8,9],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2,1],[3],[4,5,6],[9],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2,1],[3],[4],[6],[9],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2,1],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 4 1 (.system [[0,14,4,5,6,7,8,9,10,11,12,13],[1,2,3]]) (.forbid 0 4 2 (.system [[0,14,15,4],[1],[3],[6,7,8,9,10,11,12,13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4],[1,2,3],[6],[9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4],[1],[3],[6],[9,10,11,12,13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4],[1],[3],[6,7,8,9],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4],[1,2,3],[6],[9],[13]]) (.forbid 0 5 1 (.system [[0,14,5,4],[1],[3],[6,7,8,9,10,11,12,13]]) (certificate_1311_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates042
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1312_part_1 : FiniteCertificate := .forbid 3 7 1 (.system [[0],[1,2,3,15,7,8,9,10,11,12,13,14],[4],[6]]) (.forbid 4 5 1 (.system [[0],[1],[3],[4,15,5,6,7,8,9,10,11,12,13,14]]) (.forbid 4 5 2 (.system [[0],[1,2,3],[4,15,16,5,6],[9,10,11,12,13,14]]) (.forbid 4 5 3 (.system [[0],[1],[3],[4,15,16,17,5,6],[9,10,11,12,13,14]]) (.forbid 4 5 4 (.system [[0],[1],[3],[4,15,16,17,18,5,6],[9,10,11,12,13,14]]) (.forbid 4 5 5 (.system [[0],[1],[3],[4,15,16,17,18,19,5,6,7,8,9],[14]]) (.forbid 4 5 6 (.system [[0],[1,2,3],[4,15,16,17,18,19,20,5,6],[9],[14]]) (.forbid 4 7 1 (.system [[0],[1,2,3],[4,15,7,8,9,10,11,12,13,14],[6]]) (.forbid 4 7 2 (.system [[0],[1,2,3],[4,15,16,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 3 (.system [[0],[1],[3],[4,15,16,17,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 4 (.system [[0],[1],[3],[4,15,16,17,18,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 5 (.system [[0],[1],[3],[4,15,16,17,18,19,7,6],[9,10,11,12,13,14]]) (.forbid 4 7 6 (.system [[0],[1,2,3],[4,15,16,17,18,19,20,7,6],[9],[14]]) (.forbid 4 8 1 (.system [[0],[1,2,3],[4,15,8,7,6],[9,10,11,12,13,14]]) (.forbid 5 6 1 (.system [[0],[1],[3],[4,5,15,6,7,8,9,10,11,12,13,14]]) (.forbid 5 7 1 (.system [[0],[1,2,3],[4,5,15,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 2 (.system [[0],[1],[3],[4,5,15,16,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 3 (.system [[0],[1],[3],[4,5,15,16,17,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 4 (.system [[0],[1],[3],[4,5,15,16,17,18,7,6],[9,10,11,12,13,14]]) (.forbid 5 7 5 (.system [[0],[1,2,3],[4,5,15,16,17,18,19,7,6],[9],[14]]) (certificate_1312_part_0))))))))))))))))))))

noncomputable def certificate_1312_part_2 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1,2,15,16,4,5,6],[3],[9,10,11,12,13,14]]) (.forbid 2 4 3 (.system [[0],[1,2,15,16,17,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 2 4 4 (.system [[0],[1,2,15,16,17,18,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 2 4 5 (.system [[0],[1,2,15,16,17,18,19,4],[3],[6,7,8,9],[14]]) (.forbid 2 4 6 (.system [[0],[1,2,15,16,17,18,19,20,4,5,6],[3],[9],[14]]) (.forbid 2 5 1 (.system [[0],[1,2,15,5,4],[3],[6,7,8,9,10,11,12,13,14]]) (.forbid 2 5 2 (.system [[0],[1,2,15,16,5,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 2 5 3 (.system [[0],[1,2,15,16,17,5,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 2 5 4 (.system [[0],[1,2,15,16,17,18,5,4],[3],[6,7,8,9],[14]]) (.forbid 2 5 5 (.system [[0],[1,2,15,16,17,18,19,5,4],[3],[6,7,8,9],[14]]) (.forbid 2 5 6 (.system [[0],[1,2,15,16,17,18,19,20,5,4],[3],[6],[9],[14]]) (.forbid 2 6 1 (.system [[0],[1,2,15,6,7,8,9,10,11,12,13,14],[3],[4]]) (.forbid 2 7 1 (.system [[0],[1,2,15,7,6,5,4],[3],[9,10,11,12,13,14]]) (.forbid 2 7 2 (.system [[0],[1,2,15,16,7,6],[3],[4],[9,10,11,12,13,14]]) (.forbid 2 7 3 (.system [[0],[1,2,15,16,17,7,6],[3],[4],[9,10,11,12,13,14]]) (.forbid 2 7 4 (.system [[0],[1,2,15,16,17,18,7,6],[3],[4],[9,10,11,12,13,14]]) (.forbid 2 7 5 (.system [[0],[1,2,15,16,17,18,19,7,6,5,4],[3],[9],[14]]) (.forbid 2 7 6 (.system [[0],[1,2,15,16,17,18,19,20,7,6],[3],[4],[9],[14]]) (.forbid 3 4 1 (.system [[0],[1,2,3,15,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 3 5 1 (.system [[0],[1],[3,15,5,4],[6,7,8,9,10,11,12,13,14]]) (certificate_1312_part_1))))))))))))))))))))

noncomputable def certificate_1312_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[3,2,1,15,16,17,4],[6],[9,10,11,12,13,14]]) (.forbid 1 4 4 (.system [[0],[1,15,16,17,18,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 1 4 5 (.system [[0],[1,15,16,17,18,19,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 1 4 6 (.system [[0],[1,15,16,17,18,19,20,4],[3],[6,7,8,9],[14]]) (.forbid 1 5 1 (.system [[0],[1,15,5,4],[3],[6,7,8,9,10,11,12,13,14]]) (.forbid 1 5 2 (.system [[0],[3,2,1,15,16,5,4],[6],[9,10,11,12,13,14]]) (.forbid 1 5 3 (.system [[0],[1,15,16,17,5,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 1 5 4 (.system [[0],[1,15,16,17,18,5,4],[3],[6],[9,10,11,12,13,14]]) (.forbid 1 5 5 (.system [[0],[1,15,16,17,18,19,5,4],[3],[6,7,8,9],[14]]) (.forbid 1 5 6 (.system [[0],[3,2,1,15,16,17,18,19,20,5,4],[6],[9],[14]]) (.forbid 1 7 1 (.system [[0],[3,2,1,15,7,8,9,10,11,12,13,14],[4],[6]]) (.forbid 1 7 2 (.system [[0],[3,2,1,15,16,7,6],[4],[9,10,11,12,13,14]]) (.forbid 1 7 3 (.system [[0],[1,15,16,17,7,6],[3],[4],[9,10,11,12,13,14]]) (.forbid 1 7 4 (.system [[0],[1,15,16,17,18,7,6],[3],[4],[9,10,11,12,13,14]]) (.forbid 1 7 5 (.system [[0],[1,15,16,17,18,19,7,6],[3],[4],[9,10,11,12,13,14]]) (.forbid 1 7 6 (.system [[0],[3,2,1,15,16,17,18,19,20,7,6],[4],[9],[14]]) (.forbid 1 8 1 (.system [[0],[3,2,1,15,8,7,6],[4],[9,10,11,12,13,14]]) (.forbid 1 10 1 (.system [[0],[3,2,1,15,10,11,12,13,14],[4],[6,7,8,9]]) (.forbid 2 3 1 (.system [[0],[1,2,15,3],[4],[6,7,8,9,10,11,12,13,14]]) (.forbid 2 4 1 (.system [[0],[1,2,15,4],[3],[6,7,8,9,10,11,12,13,14]]) (certificate_1312_part_2))))))))))))))))))))

noncomputable def certificate_1312_part_4 : FiniteCertificate := .forbid 0 5 2 (.system [[0,15,16,5,4],[1,2,3],[6],[9,10,11,12,13,14]]) (.forbid 0 5 3 (.system [[0,15,16,17,5,4],[1],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 5 4 (.system [[0,15,16,17,18,5,4],[1],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 5 5 (.system [[0,15,16,17,18,19,5,4],[1],[3],[6,7,8,9],[14]]) (.forbid 0 5 6 (.system [[0,15,16,17,18,19,20,5,4],[1,2,3],[6],[9],[14]]) (.forbid 0 7 1 (.system [[0,15,7,8,9,10,11,12,13,14],[1,2,3],[4],[6]]) (.forbid 0 7 2 (.system [[0,15,16,7,6],[1,2,3],[4],[9,10,11,12,13,14]]) (.forbid 0 7 3 (.system [[0,15,16,17,7,6],[1],[3],[4],[9,10,11,12,13,14]]) (.forbid 0 7 4 (.system [[0,15,16,17,18,7,6],[1],[3],[4],[9,10,11,12,13,14]]) (.forbid 0 7 5 (.system [[0,15,16,17,18,19,7,6],[1],[3],[4],[9,10,11,12,13,14]]) (.forbid 0 7 6 (.system [[0,15,16,17,18,19,20,7,6],[1,2,3],[4],[9],[14]]) (.forbid 0 8 1 (.system [[0,15,8,7,6],[1,2,3],[4],[9,10,11,12,13,14]]) (.forbid 1 2 1 (.system [[0],[1,15,2,3],[4],[6,7,8,9,10,11,12,13,14]]) (.forbid 1 2 2 (.system [[0],[1,15,16,2,3],[4,5,6],[9,10,11,12,13,14]]) (.forbid 1 2 3 (.system [[0],[1,15,16,17,2,3],[4],[6],[9,10,11,12,13,14]]) (.forbid 1 2 4 (.system [[0],[1,15,16,17,18,2,3],[4],[6],[9,10,11,12,13,14]]) (.forbid 1 2 5 (.system [[0],[1,15,16,17,18,19,2,3],[4],[6,7,8,9],[14]]) (.forbid 1 2 6 (.system [[0],[1,15,16,17,18,19,20,2,3],[4,5,6],[9],[14]]) (.forbid 1 4 1 (.system [[0],[3,2,1,15,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 1 4 2 (.system [[0],[1,15,16,4],[3],[6,7,8,9,10,11,12,13,14]]) (certificate_1312_part_3))))))))))))))))))))

noncomputable def certificate_1312 : FiniteCertificate := .forbid 0 1 1 (.system [[0,15,1,2,3],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 2 (.system [[0,15,16,1],[3],[4],[6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 3 (.system [[0,15,16,17,1,2,3],[4],[6],[9,10,11,12,13,14]]) (.forbid 0 1 4 (.system [[0,15,16,17,18,1],[3],[4],[6],[9,10,11,12,13,14]]) (.forbid 0 1 5 (.system [[0,15,16,17,18,19,1],[3],[4],[6],[9,10,11,12,13,14]]) (.forbid 0 1 6 (.system [[0,15,16,17,18,19,20,1],[3],[4],[6,7,8,9],[14]]) (.forbid 0 2 1 (.system [[0,15,2,1],[3],[4],[6,7,8,9,10,11,12,13,14]]) (.forbid 0 2 2 (.system [[0,15,16,2,1],[3],[4,5,6],[9,10,11,12,13,14]]) (.forbid 0 2 3 (.system [[0,15,16,17,2,1],[3],[4],[6],[9,10,11,12,13,14]]) (.forbid 0 2 4 (.system [[0,15,16,17,18,2,1],[3],[4],[6],[9,10,11,12,13,14]]) (.forbid 0 2 5 (.system [[0,15,16,17,18,19,2,1],[3],[4],[6,7,8,9],[14]]) (.forbid 0 2 6 (.system [[0,15,16,17,18,19,20,2,1],[3],[4,5,6],[9],[14]]) (.forbid 0 3 1 (.system [[0,15,3,2,1],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 4 1 (.system [[0,15,4,5,6,7,8,9,10,11,12,13,14],[1,2,3]]) (.forbid 0 4 2 (.system [[0,15,16,4],[1],[3],[6,7,8,9,10,11,12,13,14]]) (.forbid 0 4 3 (.system [[0,15,16,17,4],[1,2,3],[6],[9,10,11,12,13,14]]) (.forbid 0 4 4 (.system [[0,15,16,17,18,4],[1],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 4 5 (.system [[0,15,16,17,18,19,4],[1],[3],[6],[9,10,11,12,13,14]]) (.forbid 0 4 6 (.system [[0,15,16,17,18,19,20,4],[1],[3],[6,7,8,9],[14]]) (.forbid 0 5 1 (.system [[0,15,5,4],[1],[3],[6,7,8,9,10,11,12,13,14]]) (certificate_1312_part_4))))))))))))))))))))

noncomputable def certificate_1326_part_2 : FiniteCertificate := .forbid 1 4 4 (.system [[0],[3,2,1,14,15,16,17,4,5,6,7],[10],[13]]) (.forbid 1 4 5 (.system [[0],[1,14,15,16,17,18,4,5,6,7],[3],[10],[13]]) (.forbid 1 4 6 (.system [[0],[3,2,1,14,15,16,17,18,19,4],[7],[10],[13]]) (.forbid 1 5 1 (.system [[0],[1,14,5,6,7,8,9,10,11,12,13],[3],[4]]) (.forbid 1 5 2 (.system [[0],[1,14,15,5,4],[3],[7,8,9,10,11,12,13]]) (.forbid 1 5 3 (.system [[0],[3,2,1,14,15,16,5,4],[7,8,9,10],[13]]) (.forbid 1 5 4 (.system [[0],[1,14,15,16,17,5,4],[3],[7,8,9,10],[13]]) (.forbid 1 5 5 (.system [[0],[3,2,1,14,15,16,17,18,5,4],[7],[10],[13]]) (.forbid 1 5 6 (.system [[0],[1,14,15,16,17,18,19,5,4],[3],[7],[10],[13]]) (.forbid 1 6 1 (.system [[0],[1,14,6,5,4],[3],[7,8,9,10,11,12,13]]) (.forbid 1 8 1 (.system [[0],[1,14,8,9,10,11,12,13],[3],[4,5,6,7]]) (.forbid 1 8 2 (.system [[0],[1,14,15,8,7,6,5,4],[3],[10,11,12,13]]) (.forbid 1 8 3 (.system [[0],[3,2,1,14,15,16,8,7,6,5,4],[10],[13]]) (.forbid 1 8 4 (.system [[0],[1,14,15,16,17,8,7,6,5,4],[3],[10],[13]]) (.forbid 1 8 5 (.system [[0],[3,2,1,14,15,16,17,18,8,7],[4],[10],[13]]) (.forbid 1 8 6 (.system [[0],[1,14,15,16,17,18,19,8,7],[3],[4],[10],[13]]) (.forbid 2 3 1 (.system [[0],[1,2,14,3],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[1,2,14,4,5,6,7,8,9,10,11,12,13],[3]]) (.forbid 2 4 2 (.system [[0],[1,2,14,15,4,5,6,7,8,9,10],[3],[13]]) (.forbid 2 4 3 (.system [[0],[1,2,14,15,16,4,5,6,7,8,9,10],[3],[13]]) (certificate_1326_part_1))))))))))))))))))))

noncomputable def certificate_1326_part_3 : FiniteCertificate := .forbid 0 5 2 (.system [[0,14,15,5,4],[1],[3],[7,8,9,10,11,12,13]]) (.forbid 0 5 3 (.system [[0,14,15,16,5,4],[1,2,3],[7,8,9,10],[13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5,4],[1],[3],[7,8,9,10],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,4],[1,2,3],[7],[10],[13]]) (.forbid 0 5 6 (.system [[0,14,15,16,17,18,19,5,4],[1],[3],[7],[10],[13]]) (.forbid 0 8 1 (.system [[0,14,8,9,10,11,12,13],[1],[3],[4,5,6,7]]) (.forbid 0 8 2 (.system [[0,14,15,8,7,6,5,4],[1],[3],[10,11,12,13]]) (.forbid 0 8 3 (.system [[0,14,15,16,8,7,6,5,4],[1,2,3],[10],[13]]) (.forbid 0 8 4 (.system [[0,14,15,16,17,8,7,6,5,4],[1],[3],[10],[13]]) (.forbid 0 8 5 (.system [[0,14,15,16,17,18,8,7],[1,2,3],[4],[10],[13]]) (.forbid 0 8 6 (.system [[0,14,15,16,17,18,19,8,7],[1],[3],[4],[10],[13]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2,3],[4,5,6,7,8,9,10],[13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2,3],[4,5,6,7,8,9,10],[13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2,3],[4,5,6,7],[10],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2,3],[4,5,6,7],[10],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2,3],[4],[7],[10],[13]]) (.forbid 1 4 1 (.system [[0],[3,2,1,14,4,5,6,7,8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4,5,6,7,8,9,10,11,12,13],[3]]) (.forbid 1 4 3 (.system [[0],[1,14,15,16,4,5,6,7,8,9,10],[3],[13]]) (certificate_1326_part_2))))))))))))))))))))

noncomputable def certificate_1326 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[3],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[3],[4,5,6,7,8,9,10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2,3],[4,5,6,7],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[3],[4,5,6,7],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2,3],[4],[7],[10],[13]]) (.forbid 0 2 1 (.system [[0,14,2,1],[3],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2,1],[3],[4,5,6,7,8,9,10],[13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2,1],[3],[4,5,6,7,8,9,10],[13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2,1],[3],[4,5,6,7],[10],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2,1],[3],[4,5,6,7],[10],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2,1],[3],[4],[7],[10],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2,1],[4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 4 1 (.system [[0,14,4,5,6,7,8,9,10,11,12,13],[1,2,3]]) (.forbid 0 4 2 (.system [[0,14,15,4,5,6,7,8,9,10,11,12,13],[1],[3]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,5,6,7,8,9,10],[1],[3],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,5,6,7],[1,2,3],[10],[13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,5,6,7],[1],[3],[10],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4],[1,2,3],[7],[10],[13]]) (.forbid 0 5 1 (.system [[0,14,5,6,7,8,9,10,11,12,13],[1],[3],[4]]) (certificate_1326_part_3))))))))))))))))))))

noncomputable def certificate_1327_part_1 : FiniteCertificate := .forbid 3 8 1 (.system [[0],[1],[3,15,8,9,10,11,12,13,14],[4,5,6,7]]) (.forbid 4 5 1 (.system [[0],[1],[3],[4,15,5,6,7,8,9,10,11,12,13,14]]) (.forbid 4 5 2 (.system [[0],[1,2,3],[4,15,16,5,6,7],[10,11,12,13,14]]) (.forbid 4 5 3 (.system [[0],[1],[3],[4,15,16,17,5,6,7],[10,11,12,13,14]]) (.forbid 4 5 4 (.system [[0],[1],[3],[4,15,16,17,18,5,6,7,8,9,10],[14]]) (.forbid 4 5 5 (.system [[0],[1,2,3],[4,15,16,17,18,19,5,6,7],[10],[14]]) (.forbid 4 5 6 (.system [[0],[1],[3],[4,15,16,17,18,19,20,5,6,7],[10],[14]]) (.forbid 4 8 1 (.system [[0],[1],[3],[7,6,5,4,15,8,9,10,11,12,13,14]]) (.forbid 4 8 2 (.system [[0],[1,2,3],[4,15,16,8,9,10,11,12,13,14],[7]]) (.forbid 4 8 3 (.system [[0],[1,2,3],[4,15,16,17,8,7],[10,11,12,13,14]]) (.forbid 4 8 4 (.system [[0],[1],[3],[4,15,16,17,18,8,7],[10,11,12,13,14]]) (.forbid 4 8 5 (.system [[0],[1],[3],[4,15,16,17,18,19,8,7],[10,11,12,13,14]]) (.forbid 4 8 6 (.system [[0],[1,2,3],[4,15,16,17,18,19,20,8,7],[10],[14]]) (.forbid 4 11 1 (.system [[0],[1],[3],[10,9,8,7,6,5,4,15,11,12,13,14]]) (.forbid 5 6 1 (.system [[0],[1],[3],[4,5,15,6,7,8,9,10,11,12,13,14]]) (.forbid 5 8 1 (.system [[0],[1,2,3],[4,5,15,8,9,10,11,12,13,14],[7]]) (.forbid 5 8 2 (.system [[0],[1,2,3],[4,5,15,16,8,7],[10,11,12,13,14]]) (.forbid 5 8 3 (.system [[0],[1],[3],[4,5,15,16,17,8,7],[10,11,12,13,14]]) (.forbid 5 8 4 (.system [[0],[1],[3],[4,5,15,16,17,18,8,7],[10,11,12,13,14]]) (.forbid 5 8 5 (.system [[0],[1,2,3],[4,5,15,16,17,18,19,8,7],[10],[14]]) (certificate_1327_part_0))))))))))))))))))))

noncomputable def certificate_1327_part_2 : FiniteCertificate := .forbid 2 4 2 (.system [[0],[1,2,15,16,4,5,6,7],[3],[10,11,12,13,14]]) (.forbid 2 4 3 (.system [[0],[1,2,15,16,17,4,5,6,7,8,9,10],[3],[14]]) (.forbid 2 4 4 (.system [[0],[1,2,15,16,17,18,4],[3],[7],[10,11,12,13,14]]) (.forbid 2 4 5 (.system [[0],[1,2,15,16,17,18,19,4,5,6,7],[3],[10],[14]]) (.forbid 2 4 6 (.system [[0],[1,2,15,16,17,18,19,20,4,5,6,7],[3],[10],[14]]) (.forbid 2 5 1 (.system [[0],[1,2,15,5,4],[3],[7,8,9,10,11,12,13,14]]) (.forbid 2 5 2 (.system [[0],[1,2,15,16,5,4],[3],[7,8,9,10,11,12,13,14]]) (.forbid 2 5 3 (.system [[0],[1,2,15,16,17,5,4],[3],[7],[10,11,12,13,14]]) (.forbid 2 5 4 (.system [[0],[1,2,15,16,17,18,5,4],[3],[7,8,9,10],[14]]) (.forbid 2 5 5 (.system [[0],[1,2,15,16,17,18,19,5,4],[3],[7,8,9,10],[14]]) (.forbid 2 5 6 (.system [[0],[1,2,15,16,17,18,19,20,5,4],[3],[7],[10],[14]]) (.forbid 2 6 1 (.system [[0],[1,2,15,6,5,4],[3],[7,8,9,10,11,12,13,14]]) (.forbid 2 8 1 (.system [[0],[1,2,15,8,7,6,5,4],[3],[10,11,12,13,14]]) (.forbid 2 8 2 (.system [[0],[1,2,15,16,8,7,6,5,4],[3],[10,11,12,13,14]]) (.forbid 2 8 3 (.system [[0],[1,2,15,16,17,8,7],[3],[4],[10,11,12,13,14]]) (.forbid 2 8 4 (.system [[0],[1,2,15,16,17,18,8,7,6,5,4],[3],[10],[14]]) (.forbid 2 8 5 (.system [[0],[1,2,15,16,17,18,19,8,7,6,5,4],[3],[10],[14]]) (.forbid 2 8 6 (.system [[0],[1,2,15,16,17,18,19,20,8,7],[3],[4],[10],[14]]) (.forbid 3 4 1 (.system [[0],[1,2,3,15,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 3 5 1 (.system [[0],[1],[3,15,5,6,7,8,9,10,11,12,13,14],[4]]) (certificate_1327_part_1))))))))))))))))))))

noncomputable def certificate_1327_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0],[1,15,16,17,4,5,6,7],[3],[10,11,12,13,14]]) (.forbid 1 4 4 (.system [[0],[3,2,1,15,16,17,18,4],[7],[10,11,12,13,14]]) (.forbid 1 4 5 (.system [[0],[1,15,16,17,18,19,4],[3],[7],[10,11,12,13,14]]) (.forbid 1 4 6 (.system [[0],[1,15,16,17,18,19,20,4,5,6,7],[3],[10],[14]]) (.forbid 1 5 1 (.system [[0],[1,15,5,6,7,8,9,10,11,12,13,14],[3],[4]]) (.forbid 1 5 2 (.system [[0],[1,15,16,5,4],[3],[7,8,9,10,11,12,13,14]]) (.forbid 1 5 3 (.system [[0],[3,2,1,15,16,17,5,4],[7],[10,11,12,13,14]]) (.forbid 1 5 4 (.system [[0],[1,15,16,17,18,5,4],[3],[7],[10,11,12,13,14]]) (.forbid 1 5 5 (.system [[0],[1,15,16,17,18,19,5,4],[3],[7,8,9,10],[14]]) (.forbid 1 5 6 (.system [[0],[3,2,1,15,16,17,18,19,20,5,4],[7],[10],[14]]) (.forbid 1 6 1 (.system [[0],[1,15,6,5,4],[3],[7,8,9,10,11,12,13,14]]) (.forbid 1 8 1 (.system [[0],[1,15,8,9,10,11,12,13,14],[3],[4,5,6,7]]) (.forbid 1 8 2 (.system [[0],[1,15,16,8,7,6,5,4],[3],[10,11,12,13,14]]) (.forbid 1 8 3 (.system [[0],[3,2,1,15,16,17,8,7],[4],[10,11,12,13,14]]) (.forbid 1 8 4 (.system [[0],[1,15,16,17,18,8,7],[3],[4],[10,11,12,13,14]]) (.forbid 1 8 5 (.system [[0],[1,15,16,17,18,19,8,7,6,5,4],[3],[10],[14]]) (.forbid 1 8 6 (.system [[0],[3,2,1,15,16,17,18,19,20,8,7],[4],[10],[14]]) (.forbid 1 9 1 (.system [[0],[1,15,9,8,7,6,5,4],[3],[10,11,12,13,14]]) (.forbid 2 3 1 (.system [[0],[1,2,15,3],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 2 4 1 (.system [[0],[1,2,15,4,5,6,7,8,9,10,11,12,13,14],[3]]) (certificate_1327_part_2))))))))))))))))))))

noncomputable def certificate_1327_part_4 : FiniteCertificate := .forbid 0 5 2 (.system [[0,15,16,5,4],[1],[3],[7,8,9,10,11,12,13,14]]) (.forbid 0 5 3 (.system [[0,15,16,17,5,4],[1,2,3],[7],[10,11,12,13,14]]) (.forbid 0 5 4 (.system [[0,15,16,17,18,5,4],[1],[3],[7],[10,11,12,13,14]]) (.forbid 0 5 5 (.system [[0,15,16,17,18,19,5,4],[1],[3],[7,8,9,10],[14]]) (.forbid 0 5 6 (.system [[0,15,16,17,18,19,20,5,4],[1,2,3],[7],[10],[14]]) (.forbid 0 6 1 (.system [[0,15,6,5,4],[1],[3],[7,8,9,10,11,12,13,14]]) (.forbid 0 8 1 (.system [[0,15,8,9,10,11,12,13,14],[1],[3],[4,5,6,7]]) (.forbid 0 8 2 (.system [[0,15,16,8,7,6,5,4],[1],[3],[10,11,12,13,14]]) (.forbid 0 8 3 (.system [[0,15,16,17,8,7],[1,2,3],[4],[10,11,12,13,14]]) (.forbid 0 8 4 (.system [[0,15,16,17,18,8,7],[1],[3],[4],[10,11,12,13,14]]) (.forbid 0 8 5 (.system [[0,15,16,17,18,19,8,7,6,5,4],[1],[3],[10],[14]]) (.forbid 0 8 6 (.system [[0,15,16,17,18,19,20,8,7],[1,2,3],[4],[10],[14]]) (.forbid 1 2 1 (.system [[0],[1,15,2,3],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 1 2 2 (.system [[0],[1,15,16,2,3],[4,5,6,7],[10,11,12,13,14]]) (.forbid 1 2 3 (.system [[0],[1,15,16,17,2,3],[4,5,6,7,8,9,10],[14]]) (.forbid 1 2 4 (.system [[0],[1,15,16,17,18,2,3],[4],[7],[10,11,12,13,14]]) (.forbid 1 2 5 (.system [[0],[1,15,16,17,18,19,2,3],[4,5,6,7],[10],[14]]) (.forbid 1 2 6 (.system [[0],[1,15,16,17,18,19,20,2,3],[4,5,6,7],[10],[14]]) (.forbid 1 4 1 (.system [[0],[3,2,1,15,4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 1 4 2 (.system [[0],[1,15,16,4,5,6,7,8,9,10,11,12,13,14],[3]]) (certificate_1327_part_3))))))))))))))))))))

noncomputable def certificate_1327 : FiniteCertificate := .forbid 0 1 1 (.system [[0,15,1,2,3],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 2 (.system [[0,15,16,1],[3],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 1 3 (.system [[0,15,16,17,1],[3],[4,5,6,7],[10,11,12,13,14]]) (.forbid 0 1 4 (.system [[0,15,16,17,18,1,2,3],[4],[7],[10,11,12,13,14]]) (.forbid 0 1 5 (.system [[0,15,16,17,18,19,1],[3],[4],[7],[10,11,12,13,14]]) (.forbid 0 1 6 (.system [[0,15,16,17,18,19,20,1],[3],[4,5,6,7],[10],[14]]) (.forbid 0 2 1 (.system [[0,15,2,1],[3],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 2 2 (.system [[0,15,16,2,1],[3],[4,5,6,7],[10,11,12,13,14]]) (.forbid 0 2 3 (.system [[0,15,16,17,2,1],[3],[4,5,6,7,8,9,10],[14]]) (.forbid 0 2 4 (.system [[0,15,16,17,18,2,1],[3],[4],[7],[10,11,12,13,14]]) (.forbid 0 2 5 (.system [[0,15,16,17,18,19,2,1],[3],[4,5,6,7],[10],[14]]) (.forbid 0 2 6 (.system [[0,15,16,17,18,19,20,2,1],[3],[4,5,6,7],[10],[14]]) (.forbid 0 3 1 (.system [[0,15,3,2,1],[4,5,6,7,8,9,10,11,12,13,14]]) (.forbid 0 4 1 (.system [[0,15,4,5,6,7,8,9,10,11,12,13,14],[1,2,3]]) (.forbid 0 4 2 (.system [[0,15,16,4,5,6,7,8,9,10,11,12,13,14],[1],[3]]) (.forbid 0 4 3 (.system [[0,15,16,17,4,5,6,7],[1],[3],[10,11,12,13,14]]) (.forbid 0 4 4 (.system [[0,15,16,17,18,4],[1,2,3],[7],[10,11,12,13,14]]) (.forbid 0 4 5 (.system [[0,15,16,17,18,19,4],[1],[3],[7],[10,11,12,13,14]]) (.forbid 0 4 6 (.system [[0,15,16,17,18,19,20,4,5,6,7],[1],[3],[10],[14]]) (.forbid 0 5 1 (.system [[0,15,5,6,7,8,9,10,11,12,13,14],[1],[3],[4]]) (certificate_1327_part_4))))))))))))))))))))

noncomputable def certificate_1341_part_2 : FiniteCertificate := .forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4,3],[5],[7],[8],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4,3],[5],[7],[8],[11]]) (.forbid 1 6 1 (.system [[0],[3,2,1,12,6,5],[7],[8,9,10,11]]) (.forbid 1 6 2 (.system [[0],[1,12,13,6,5],[3],[7],[8,9,10,11]]) (.forbid 1 6 3 (.system [[0],[3,2,1,12,13,14,6,5],[7],[8],[11]]) (.forbid 1 6 4 (.system [[0],[1,12,13,14,15,6,5],[3],[7],[8],[11]]) (.forbid 1 6 5 (.system [[0],[1,12,13,14,15,16,6,5],[3],[7],[8],[11]]) (.forbid 1 6 6 (.system [[0],[1,12,13,14,15,16,17,6,5],[3],[7],[8],[11]]) (.forbid 1 8 1 (.system [[0],[7,6,5,4,3,2,1,12,8,9,10,11]]) (.forbid 1 8 2 (.system [[0],[3,2,1,12,13,8,9,10,11],[5],[7]]) (.forbid 1 8 3 (.system [[0],[1,12,13,14,8,9,10,11],[3],[5],[7]]) (.forbid 1 8 4 (.system [[0],[3,2,1,12,13,14,15,8],[5],[7],[11]]) (.forbid 1 8 5 (.system [[0],[1,12,13,14,15,16,8],[3],[5],[7],[11]]) (.forbid 1 8 6 (.system [[0],[1,12,13,14,15,16,17,8],[3],[5],[7],[11]]) (.forbid 2 4 1 (.system [[0],[1,2,12,4,3],[5],[7],[8,9,10,11]]) (.forbid 2 4 2 (.system [[0],[1,2,12,13,4,3],[5,6,7],[8],[11]]) (.forbid 2 4 3 (.system [[0],[1,2,12,13,14,4,3],[5],[7],[8],[11]]) (.forbid 2 4 4 (.system [[0],[1,2,12,13,14,15,4,3],[5],[7],[8],[11]]) (.forbid 2 4 5 (.system [[0],[1,2,12,13,14,15,16,4,3],[5],[7],[8],[11]]) (.forbid 2 4 6 (.system [[0],[1,2,12,13,14,15,16,17,4,3],[5],[7],[8],[11]]) (certificate_1341_part_1))))))))))))))))))))

noncomputable def certificate_1341_part_3 : FiniteCertificate := .forbid 0 6 3 (.system [[0,12,13,14,6,5],[1,2,3],[7],[8],[11]]) (.forbid 0 6 4 (.system [[0,12,13,14,15,6,5],[1],[3],[7],[8],[11]]) (.forbid 0 6 5 (.system [[0,12,13,14,15,16,6,5],[1],[3],[7],[8],[11]]) (.forbid 0 6 6 (.system [[0,12,13,14,15,16,17,6,5],[1],[3],[7],[8],[11]]) (.forbid 0 8 1 (.system [[0,12,8,9,10,11],[1,2,3,4,5,6,7]]) (.forbid 0 8 2 (.system [[0,12,13,8,9,10,11],[1,2,3],[5],[7]]) (.forbid 0 8 3 (.system [[0,12,13,14,8,9,10,11],[1],[3],[5],[7]]) (.forbid 0 8 4 (.system [[0,12,13,14,15,8],[1,2,3],[5],[7],[11]]) (.forbid 0 8 5 (.system [[0,12,13,14,15,16,8],[1],[3],[5],[7],[11]]) (.forbid 0 8 6 (.system [[0,12,13,14,15,16,17,8],[1],[3],[5],[7],[11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3,4,5],[7],[8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3],[5],[7],[8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2,3,4,5],[7],[8],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2,3],[5],[7],[8],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2,3],[5],[7],[8],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2,3],[5],[7],[8],[11]]) (.forbid 1 4 1 (.system [[0],[1,12,4,3],[5,6,7],[8,9,10,11]]) (.forbid 1 4 2 (.system [[0],[1,12,13,4,3],[5],[7],[8,9,10,11]]) (.forbid 1 4 3 (.system [[0],[1,12,13,14,4,3],[5,6,7],[8],[11]]) (.forbid 1 4 4 (.system [[0],[1,12,13,14,15,4,3],[5],[7],[8],[11]]) (certificate_1341_part_2))))))))))))))))))))

noncomputable def certificate_1341 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2,3,4,5,6,7],[8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1,2,3],[5],[7],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[3],[5],[7],[8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1,2,3],[5],[7],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[3],[5],[7],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[3],[5],[7],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2,1],[3,4,5],[7],[8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2,1],[3],[5],[7],[8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2,1],[3,4,5],[7],[8],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2,1],[3],[5],[7],[8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2,1],[3],[5],[7],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2,1],[3],[5],[7],[8],[11]]) (.forbid 0 4 1 (.system [[0,12,4,3,2,1],[5],[7],[8,9,10,11]]) (.forbid 0 4 2 (.system [[0,12,13,4,3],[1],[5],[7],[8,9,10,11]]) (.forbid 0 4 3 (.system [[0,12,13,14,4,3,2,1],[5],[7],[8],[11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4,3],[1],[5],[7],[8],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4,3],[1],[5],[7],[8],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4,3],[1],[5],[7],[8],[11]]) (.forbid 0 6 1 (.system [[0,12,6,5],[1,2,3],[7],[8,9,10,11]]) (.forbid 0 6 2 (.system [[0,12,13,6,5],[1],[3],[7],[8,9,10,11]]) (certificate_1341_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates043
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1356_part_3 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[1],[3],[8],[9,10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[1],[3],[8],[9,10,11,12,13]]) (.forbid 0 6 5 (.system [[0,14,15,16,17,18,6,5],[1,2,3],[8],[9],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[1],[3],[8],[9],[13]]) (.forbid 0 7 1 (.system [[0,14,7,6,5],[1,2,3],[8],[9,10,11,12,13]]) (.forbid 0 7 2 (.system [[0,14,15,7,6,5],[1],[3],[8],[9,10,11,12,13]]) (.forbid 0 7 3 (.system [[0,14,15,16,7,6,5],[1],[3],[8],[9,10,11,12,13]]) (.forbid 0 7 4 (.system [[0,14,15,16,17,7,6,5],[1,2,3],[8],[9],[13]]) (.forbid 0 7 5 (.system [[0,14,15,16,17,18,7,6,5],[1],[3],[8],[9],[13]]) (.forbid 0 7 6 (.system [[0,14,15,16,17,18,19,7,6,5],[1],[3],[8],[9],[13]]) (.forbid 0 8 1 (.system [[0,14,8,7,6,5,4,3,2,1],[9,10,11,12,13]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2,3,4,5],[8],[9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2,3],[5],[8],[9,10,11,12,13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2,3],[5,6,7,8],[9],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2,3,4,5],[8],[9],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2,3],[5],[8],[9],[13]]) (.forbid 1 4 1 (.system [[0],[1,14,4,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0],[1,14,15,16,4,3],[5],[8],[9,10,11,12,13]]) (certificate_1356_part_2))))))))))))))))))))

end CycleClique

end OAI
end


