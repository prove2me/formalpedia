-- Prove2me | Definitions.Def_OAIQ107D134
-- name    : OAIQ107D134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T19:22:31.81983+00:00
-- url     : https://prove2.me/theorems/d7c3a344-166d-4ecb-bb87-4115bec083af
-- title:
--   Definitions bundle OAIQ107D134 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 69 definitions. The definitions and types are `OAI.CycleClique.certificate_1356`, `OAI.CycleClique.certificate_137`, `OAI.CycleClique.certificate_141`, `OAI.CycleClique.certificate_148_part_10_M`, `OAI.CycleClique.certificate_148_part_11_M`, `OAI.CycleClique.certificate_148_part_12_M`, `OAI.CycleClique.certificate_148_part_4_M`, `OAI.CycleClique.certificate_148_part_5_M`, `OAI.CycleClique.certificate_148_part_6_M`, `OAI.CycleClique.certificate_148_part_7_M`, `OAI.CycleClique.certificate_148_part_8_M`, `OAI.CycleClique.certificate_148_part_9_M`, `OAI.CycleClique.certificate_1589`, `OAI.CycleClique.certificate_1589_part_2`, `OAI.CycleClique.certificate_1589_part_3`, `OAI.CycleClique.certificate_1589_part_4`, `OAI.CycleClique.certificate_15_part_2_M`, `OAI.CycleClique.certificate_15_part_3_M`, `OAI.CycleClique.certificate_15_part_4_M`, `OAI.CycleClique.certificate_15_part_5_M`, `OAI.CycleClique.certificate_15_part_6_M`, `OAI.CycleClique.certificate_15_part_7_M`, `OAI.CycleClique.certificate_225_part_81_M`, `OAI.CycleClique.certificate_225_part_82_M`, `OAI.CycleClique.certificate_225_part_83_M`, `OAI.CycleClique.certificate_225_part_84_M`, `OAI.CycleClique.certificate_225_part_85_M`, `OAI.CycleClique.certificate_225_part_86_M`, `OAI.CycleClique.certificate_225_part_87_M`, `OAI.CycleClique.certificate_225_part_88_M`, `OAI.CycleClique.certificate_225_part_89_M`, `OAI.CycleClique.certificate_2788`, `OAI.CycleClique.certificate_2788_part_4`, `OAI.CycleClique.certificate_544_part_10_M`, `OAI.CycleClique.certificate_544_part_11_M`, `OAI.CycleClique.certificate_544_part_12_M`, `OAI.CycleClique.certificate_544_part_13_M`, `OAI.CycleClique.certificate_544_part_14_M`, `OAI.CycleClique.certificate_544_part_15_M`, `OAI.CycleClique.certificate_544_part_16_M` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Ramsey_CycleClique_Certificates001`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates001.lean), [`Ramsey_CycleClique_Certificates005`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates005.lean), [`Ramsey_CycleClique_Certificates008`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates008.lean), [`Ramsey_CycleClique_Certificates018`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates018.lean), [`Ramsey_CycleClique_Certificates043`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates043.lean), [`Ramsey_CycleClique_Certificates050`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates050.lean), [`Ramsey_CycleClique_Certificates088`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Ramsey/CycleClique/Certificates088.lean).
--
--   **Imports.** It imports the bundles `OAIQ107D126`, `OAIQ107D127`, `OAIQ107D128`, `OAIQ107D130`, `OAIQ107D131` and `OAIQ107D132` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.CycleClique.finite_patterns_10_5`, `OAI.CycleClique.finite_patterns_11_5`, `OAI.CycleClique.finite_range_verified`, `OAI.CycleClique.patterns_13_6_1_verified`, `OAI.CycleClique.patterns_15_7_12_verified`, `OAI.CycleClique.patterns_15_8_4_verified` and `OAI.CycleClique.patterns_17_8_35_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D127
import Definitions.Def_OAIQ107D128
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D132

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_15_part_2_M : ForbiddenMatrix := ((1,3,1) :: (((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,4,1) :: (((0,3,1) :: (((0,2,5) :: (certificate_15_part_1_M))))))))))))))))

noncomputable def certificate_15_part_3_M : ForbiddenMatrix := ((0,1,2) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,0) :: (((2,3,1) :: (((1,4,1) :: (certificate_15_part_2_M))))))))))))))

noncomputable def certificate_15_part_4_M : ForbiddenMatrix := ((0,4,2) :: (((0,4,0) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,0) :: (((2,3,1) :: (((1,4,1) :: (certificate_15_part_2_M))))))))))))))))

noncomputable def certificate_15_part_5_M : ForbiddenMatrix := ((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((1,4,0) :: (((1,3,0) :: (((0,4,4) :: (((0,4,3) :: (certificate_15_part_4_M))))))))))))))))

noncomputable def certificate_15_part_6_M : ForbiddenMatrix := ((0,1,2) :: (((4,5,1) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,5,5) :: (certificate_15_part_5_M))))))))))))))

noncomputable def certificate_15_part_7_M : ForbiddenMatrix := ((3,4,1) :: (((2,4,0) :: (((4,5,1) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,5,5) :: (certificate_15_part_5_M))))))))))))))))

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

noncomputable def certificate_137 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1],[2],[3],[4],[5],[6]]) (.forbid 0 1 2 (.system [[0,7,8,1],[2],[3],[4],[5],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1],[2],[3],[4],[5],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[2],[3],[4],[5],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[2],[3],[4],[5],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[2],[3],[4],[5],[6]]) (.forbid 0 2 1 (.system [[0,7,2],[1],[3],[4],[5],[6]]) (.forbid 0 2 2 (.system [[0,7,8,2],[1],[3],[4],[5],[6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2],[1],[3],[4],[5],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2],[1],[3],[4],[5],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2],[1],[3],[4],[5],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2],[1],[3],[4],[5],[6]]) (.forbid 0 3 1 (.system [[0,7,3],[1],[2],[4],[5],[6]]) (.forbid 0 3 2 (.system [[0,7,8,3],[1],[2],[4],[5],[6]]) (.forbid 0 3 3 (.system [[0,7,8,9,3],[1],[2],[4],[5],[6]]) (.forbid 0 3 4 (.system [[0,7,8,9,10,3],[1],[2],[4],[5],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3],[1],[2],[4],[5],[6]]) (.forbid 0 3 6 (.system [[0,7,8,9,10,11,12,3],[1],[2],[4],[5],[6]]) (.forbid 0 4 1 (.system [[0,7,4],[1],[2],[3],[5],[6]]) (.forbid 0 5 1 (.system [[0,7,5],[1],[2],[3],[4],[6]]) (certificate_137_part_1))))))))))))))))))))

noncomputable def certificate_141 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1],[2],[3,4,5],[6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1],[2],[3],[5],[6],[8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1],[2],[3],[5],[6],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1],[2],[3],[5],[6],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1],[2],[3],[5],[6],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[2],[3],[5],[6],[8]]) (.forbid 0 2 1 (.system [[0,9,2],[1],[3,4,5],[6,7,8]]) (.forbid 0 2 2 (.system [[0,9,10,2],[1],[3],[5],[6],[8]]) (.forbid 0 2 3 (.system [[0,9,10,11,2],[1],[3],[5],[6],[8]]) (.forbid 0 2 4 (.system [[0,9,10,11,12,2],[1],[3],[5],[6],[8]]) (.forbid 0 2 5 (.system [[0,9,10,11,12,13,2],[1],[3],[5],[6],[8]]) (.forbid 0 2 6 (.system [[0,9,10,11,12,13,14,2],[1],[3],[5],[6],[8]]) (.forbid 0 3 1 (.system [[0,9,3,4,5],[1],[2],[6,7,8]]) (.forbid 0 3 2 (.system [[0,9,10,3],[1],[2],[5],[6],[8]]) (.forbid 0 3 3 (.system [[0,9,10,11,3],[1],[2],[5],[6],[8]]) (.forbid 0 3 4 (.system [[0,9,10,11,12,3],[1],[2],[5],[6],[8]]) (.forbid 0 3 5 (.system [[0,9,10,11,12,13,3],[1],[2],[5],[6],[8]]) (.forbid 0 3 6 (.system [[0,9,10,11,12,13,14,3],[1],[2],[5],[6],[8]]) (.forbid 0 4 1 (.system [[0,9,4,3],[1],[2],[5],[6],[8]]) (.forbid 0 4 2 (.system [[0,9,10,4,3],[1],[2],[5],[6],[8]]) (certificate_141_part_1))))))))))))))))))))

noncomputable def certificate_148_part_4_M : ForbiddenMatrix := ((2,3,1) :: (((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,3,6) :: (certificate_148_part_3_M))))))))))))))))

noncomputable def certificate_148_part_5_M : ForbiddenMatrix := ((0,1,4) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (((2,4,1) :: (certificate_148_part_4_M))))))))))))))

noncomputable def certificate_148_part_6_M : ForbiddenMatrix := ((0,2,2) :: (((0,4,0) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (((3,4,2) :: (((3,4,1) :: (((2,4,1) :: (certificate_148_part_4_M))))))))))))))))

noncomputable def certificate_148_part_7_M : ForbiddenMatrix := ((2,3,2) :: (((1,2,6) :: (((1,2,5) :: (((1,2,3) :: (((1,2,2) :: (((0,2,6) :: (((0,2,5) :: (((0,2,3) :: (certificate_148_part_6_M))))))))))))))))

noncomputable def certificate_148_part_8_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,4) :: (((0,5,0) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (certificate_148_part_7_M))))))))))))))

noncomputable def certificate_148_part_9_M : ForbiddenMatrix := ((0,1,4) :: (((0,6,0) :: (((0,5,0) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (certificate_148_part_7_M))))))))))))))

noncomputable def certificate_148_part_10_M : ForbiddenMatrix := ((1,4,0) :: (((0,6,0) :: (((0,5,0) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (certificate_148_part_7_M))))))))))))))

noncomputable def certificate_148_part_11_M : ForbiddenMatrix := ((1,5,0) :: (((1,4,0) :: (((0,6,0) :: (((0,5,0) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (certificate_148_part_7_M))))))))))))))))

noncomputable def certificate_148_part_12_M : ForbiddenMatrix := ((0,2,4) :: (((2,4,6) :: (((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((1,6,0) :: (certificate_148_part_11_M))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates008
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_225_part_81_M : ForbiddenMatrix := ((1,3,4) :: (((1,2,4) :: (((1,2,3) :: (((0,4,5) :: (((0,3,5) :: (((0,3,4) :: (((0,2,4) :: (((0,2,3) :: (certificate_225_part_80_M))))))))))))))))

noncomputable def certificate_225_part_82_M : ForbiddenMatrix := ((7,8,1) :: (((4,7,0) :: (((3,5,0) :: (((8,9,4) :: (((8,9,3) :: (((8,9,2) :: (((5,9,1) :: (certificate_225_part_76_M))))))))))))))

noncomputable def certificate_225_part_83_M : ForbiddenMatrix := ((3,5,1) :: (((7,8,1) :: (((4,7,0) :: (((3,5,0) :: (((8,9,4) :: (((8,9,3) :: (((8,9,2) :: (((5,9,1) :: (certificate_225_part_76_M))))))))))))))))

noncomputable def certificate_225_part_84_M : ForbiddenMatrix := ((0,4,5) :: (((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((3,5,3) :: (((3,5,2) :: (certificate_225_part_83_M))))))))))))))

noncomputable def certificate_225_part_85_M : ForbiddenMatrix := ((1,11,1) :: (((1,11,0) :: (((0,11,5) :: (((0,11,4) :: (((0,11,3) :: (((0,11,2) :: (((0,11,1) :: (((0,11,0) :: (certificate_225_part_84_M))))))))))))))))

noncomputable def certificate_225_part_86_M : ForbiddenMatrix := ((4,11,0) :: (((4,8,0) :: (((2,11,3) :: (((2,11,2) :: (((2,11,1) :: (((2,11,0) :: (((1,11,3) :: (((1,11,2) :: (certificate_225_part_85_M))))))))))))))))

noncomputable def certificate_225_part_87_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((3,7,1) :: (((3,5,3) :: (((3,5,2) :: (certificate_225_part_83_M))))))))))))))

noncomputable def certificate_225_part_88_M : ForbiddenMatrix := ((4,9,2) :: (((4,9,1) :: (((3,7,0) :: (((3,6,0) :: (((3,7,1) :: (((3,5,3) :: (((3,5,2) :: (certificate_225_part_83_M))))))))))))))

noncomputable def certificate_225_part_89_M : ForbiddenMatrix := ((0,1,3) :: (((3,8,0) :: (((3,7,0) :: (((3,6,0) :: (((3,7,1) :: (((3,5,3) :: (((3,5,2) :: (certificate_225_part_83_M))))))))))))))

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

noncomputable def certificate_544_part_2_M : ForbiddenMatrix := ((0,3,6) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,2,2) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (certificate_544_part_1_M))))))))))))))))

noncomputable def certificate_544_part_3_M : ForbiddenMatrix := ((1,2,1) :: (((0,6,1) :: (((0,4,6) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_544_part_2_M))))))))))))))))

noncomputable def certificate_544_part_4_M : ForbiddenMatrix := ((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((1,2,2) :: (certificate_544_part_3_M))))))))))))))))

noncomputable def certificate_544_part_5_M : ForbiddenMatrix := ((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,3,6) :: (((1,3,5) :: (certificate_544_part_4_M))))))))))))))))

noncomputable def certificate_544_part_6_M : ForbiddenMatrix := ((2,4,1) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,6,1) :: (certificate_544_part_5_M))))))))))))))))

noncomputable def certificate_544_part_7_M : ForbiddenMatrix := ((3,4,2) :: (((3,4,1) :: (((2,6,1) :: (((2,4,6) :: (((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (certificate_544_part_6_M))))))))))))))))

noncomputable def certificate_544_part_8_M : ForbiddenMatrix := ((0,1,3) :: (((4,8,1) :: (((4,5,1) :: (((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (certificate_544_part_7_M))))))))))))))

noncomputable def certificate_544_part_9_M : ForbiddenMatrix := ((0,8,1) :: (((0,4,0) :: (((4,8,1) :: (((4,5,1) :: (((3,4,6) :: (((3,4,5) :: (((3,4,4) :: (((3,4,3) :: (certificate_544_part_7_M))))))))))))))))

noncomputable def certificate_544_part_10_M : ForbiddenMatrix := ((3,6,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((3,8,1) :: (((2,8,1) :: (((1,8,1) :: (certificate_544_part_9_M))))))))))))))

noncomputable def certificate_544_part_11_M : ForbiddenMatrix := ((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,5,0) :: (((3,8,1) :: (((2,8,1) :: (((1,8,1) :: (certificate_544_part_9_M))))))))))))))))

noncomputable def certificate_544_part_12_M : ForbiddenMatrix := ((4,6,2) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (certificate_544_part_11_M))))))))))))))))

noncomputable def certificate_544_part_13_M : ForbiddenMatrix := ((1,6,0) :: (((1,4,0) :: (((0,7,1) :: (((0,6,0) :: (((0,1,3) :: (((4,6,4) :: (((4,6,3) :: (certificate_544_part_12_M))))))))))))))

noncomputable def certificate_544_part_14_M : ForbiddenMatrix := ((4,6,0) :: (((3,7,1) :: (((3,6,2) :: (((3,6,1) :: (((3,6,0) :: (((2,6,0) :: (((2,4,0) :: (((1,7,1) :: (certificate_544_part_13_M))))))))))))))))

noncomputable def certificate_544_part_15_M : ForbiddenMatrix := ((0,1,3) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((4,6,4) :: (((4,6,3) :: (certificate_544_part_12_M))))))))))))))

noncomputable def certificate_544_part_16_M : ForbiddenMatrix := ((0,8,2) :: (((0,6,0) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((4,6,4) :: (((4,6,3) :: (certificate_544_part_12_M))))))))))))))))

noncomputable def certificate_544_part_17_M : ForbiddenMatrix := ((0,9,5) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,8,6) :: (((0,8,5) :: (((0,8,4) :: (((0,8,3) :: (certificate_544_part_16_M))))))))))))))))

noncomputable def certificate_544_part_18_M : ForbiddenMatrix := ((3,9,3) :: (((3,9,2) :: (((3,8,6) :: (((3,8,5) :: (((3,8,4) :: (((3,8,3) :: (((3,8,2) :: (((0,9,6) :: (certificate_544_part_17_M))))))))))))))))

noncomputable def certificate_544_part_19_M : ForbiddenMatrix := ((4,8,6) :: (((4,8,5) :: (((4,8,4) :: (((4,8,3) :: (((4,8,2) :: (((3,9,6) :: (((3,9,5) :: (((3,9,4) :: (certificate_544_part_18_M))))))))))))))))

noncomputable def certificate_544_part_20_M : ForbiddenMatrix := ((8,9,2) :: (((8,9,1) :: (((4,9,6) :: (((4,9,5) :: (((4,9,4) :: (((4,9,3) :: (((4,9,2) :: (((4,9,1) :: (certificate_544_part_19_M))))))))))))))))

noncomputable def certificate_544_part_21_M : ForbiddenMatrix := ((2,9,1) :: (((1,9,1) :: (((0,9,1) :: (((8,9,6) :: (((8,9,5) :: (((8,9,4) :: (((8,9,3) :: (certificate_544_part_20_M))))))))))))))

noncomputable def certificate_544_part_22_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((0,8,0) :: (((8,9,6) :: (((8,9,5) :: (((8,9,4) :: (((8,9,3) :: (certificate_544_part_20_M))))))))))))))

noncomputable def certificate_544_part_23_M : ForbiddenMatrix := ((0,1,3) :: (((0,9,0) :: (((0,8,0) :: (((8,9,6) :: (((8,9,5) :: (((8,9,4) :: (((8,9,3) :: (certificate_544_part_20_M))))))))))))))

noncomputable def certificate_544_part_24_M : ForbiddenMatrix := ((1,4,0) :: (((0,9,0) :: (((0,8,0) :: (((8,9,6) :: (((8,9,5) :: (((8,9,4) :: (((8,9,3) :: (certificate_544_part_20_M))))))))))))))

noncomputable def certificate_544_part_25_M : ForbiddenMatrix := ((1,5,0) :: (((1,4,0) :: (((0,9,0) :: (((0,8,0) :: (((8,9,6) :: (((8,9,5) :: (((8,9,4) :: (((8,9,3) :: (certificate_544_part_20_M))))))))))))))))

noncomputable def certificate_544_part_26_M : ForbiddenMatrix := ((3,5,1) :: (((2,5,1) :: (((1,5,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((1,8,0) :: (certificate_544_part_25_M))))))))))))))

noncomputable def certificate_544_part_27_M : ForbiddenMatrix := ((2,6,3) :: (((2,6,2) :: (((1,6,6) :: (((0,6,6) :: (((2,8,0) :: (((2,5,0) :: (((2,4,0) :: (((1,8,0) :: (certificate_544_part_25_M))))))))))))))))

noncomputable def certificate_544_part_28_M : ForbiddenMatrix := ((6,7,1) :: (((5,6,1) :: (((4,6,6) :: (((4,6,5) :: (((2,6,6) :: (((2,6,5) :: (((2,6,4) :: (certificate_544_part_27_M))))))))))))))

noncomputable def certificate_544_part_29_M : ForbiddenMatrix := ((3,5,0) :: (((6,7,1) :: (((5,6,1) :: (((4,6,6) :: (((4,6,5) :: (((2,6,6) :: (((2,6,5) :: (((2,6,4) :: (certificate_544_part_27_M))))))))))))))))

noncomputable def certificate_544_part_30_M : ForbiddenMatrix := ((0,13,0) :: (((6,8,6) :: (((6,8,5) :: (((6,8,4) :: (((6,8,3) :: (((6,8,2) :: (((6,8,1) :: (certificate_544_part_29_M))))))))))))))

noncomputable def certificate_544_part_31_M : ForbiddenMatrix := ((4,6,0) :: (((2,13,0) :: (((1,13,0) :: (((0,13,5) :: (((0,13,4) :: (((0,13,3) :: (((0,13,2) :: (((0,13,1) :: (certificate_544_part_30_M))))))))))))))))

noncomputable def certificate_544_part_32_M : ForbiddenMatrix := ((6,13,0) :: (((4,13,4) :: (((4,13,3) :: (((4,13,2) :: (((4,13,1) :: (((4,13,0) :: (((4,8,0) :: (((4,6,1) :: (certificate_544_part_31_M))))))))))))))))

noncomputable def certificate_544_part_33_M : ForbiddenMatrix := ((8,13,2) :: (((8,13,1) :: (((8,13,0) :: (((6,13,5) :: (((6,13,4) :: (((6,13,3) :: (((6,13,2) :: (((6,13,1) :: (certificate_544_part_32_M))))))))))))))))

noncomputable def certificate_544_part_34_M : ForbiddenMatrix := ((3,5,2) :: (((3,5,1) :: (((6,8,6) :: (((6,8,5) :: (((6,8,4) :: (((6,8,3) :: (((6,8,2) :: (((6,8,1) :: (certificate_544_part_29_M))))))))))))))))

noncomputable def certificate_544_part_35_M : ForbiddenMatrix := ((0,1,3) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (certificate_544_part_34_M))))))))))))))

noncomputable def certificate_544_part_36_M : ForbiddenMatrix := ((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (certificate_544_part_34_M))))))))))))))

noncomputable def certificate_544_part_37_M : ForbiddenMatrix := ((4,7,0) :: (((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((3,5,5) :: (((3,5,4) :: (((3,5,3) :: (certificate_544_part_34_M))))))))))))))))

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

noncomputable def certificate_1356 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3,4,5,6,7,8],[9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2,3],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[3],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[3],[5,6,7,8],[9],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2,3],[5],[8],[9],[13]]) (.forbid 0 2 1 (.system [[0,14,2,1],[3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2,1],[3,4,5],[8],[9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2,1],[3],[5],[8],[9,10,11,12,13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2,1],[3],[5,6,7,8],[9],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2,1],[3,4,5],[8],[9],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2,1],[3],[5],[8],[9],[13]]) (.forbid 0 4 1 (.system [[0,14,4,3],[1],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3,2,1],[5],[8],[9,10,11,12,13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,3],[1],[5],[8],[9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[1],[5,6,7,8],[9],[13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3,2,1],[5],[8],[9],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[1],[5],[8],[9],[13]]) (.forbid 0 6 1 (.system [[0,14,6,7,8],[1,2,3],[5],[9,10,11,12,13]]) (.forbid 0 6 2 (.system [[0,14,15,6,5],[1,2,3],[8],[9,10,11,12,13]]) (certificate_1356_part_3))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates050
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1589_part_2 : FiniteCertificate := .forbid 2 3 3 (.system [[0],[1],[2,14,15,16,3],[5],[7,8,9,10,11],[13]]) (.forbid 2 3 4 (.system [[0],[1],[2,14,15,16,17,3],[5],[7,8,9,10,11],[13]]) (.forbid 2 3 5 (.system [[0],[1],[2,14,15,16,17,18,3,4,5],[7],[11],[13]]) (.forbid 2 3 6 (.system [[0],[1],[2,14,15,16,17,18,19,3],[5],[7],[11],[13]]) (.forbid 2 4 1 (.system [[0],[1],[2,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 2 4 2 (.system [[0],[1],[2,14,15,4,3],[5],[7,8,9,10,11],[13]]) (.forbid 2 4 3 (.system [[0],[1],[2,14,15,16,4,3],[5],[7,8,9,10,11],[13]]) (.forbid 2 4 4 (.system [[0],[1],[2,14,15,16,17,4,3],[5,6,7],[11],[13]]) (.forbid 2 4 5 (.system [[0],[1],[2,14,15,16,17,18,4,3],[5],[7],[11],[13]]) (.forbid 2 4 6 (.system [[0],[1],[2,14,15,16,17,18,19,4,3],[5],[7],[11],[13]]) (.forbid 2 6 1 (.system [[0],[1],[2,14,6,5,4,3],[7,8,9,10,11],[13]]) (.forbid 2 6 2 (.system [[0],[1],[2,14,15,6,5],[3],[7,8,9,10,11],[13]]) (.forbid 2 6 3 (.system [[0],[1],[2,14,15,16,6,5],[3],[7,8,9,10,11],[13]]) (.forbid 2 6 4 (.system [[0],[1],[2,14,15,16,17,6,5,4,3],[7],[11],[13]]) (.forbid 2 6 5 (.system [[0],[1],[2,14,15,16,17,18,6,5],[3],[7],[11],[13]]) (.forbid 2 6 6 (.system [[0],[1],[2,14,15,16,17,18,19,6,5],[3],[7],[11],[13]]) (.forbid 2 8 1 (.system [[0],[1],[2,14,8,9,10,11],[3,4,5,6,7],[13]]) (.forbid 2 10 1 (.system [[0],[1],[2,14,10,9,8,7,6,5,4,3],[11],[13]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,14,4,5,6,7,8,9,10,11],[13]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,14,15,4,5],[7,8,9,10,11],[13]]) (certificate_1589_part_1))))))))))))))))))))

noncomputable def certificate_1589_part_3 : FiniteCertificate := .forbid 1 3 3 (.system [[0],[1,14,15,16,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 3 4 (.system [[0],[1,14,15,16,17,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 3 5 (.system [[0],[1,14,15,16,17,18,3,4,5],[2],[7],[11],[13]]) (.forbid 1 3 6 (.system [[0],[1,14,15,16,17,18,19,3],[2],[5],[7],[11],[13]]) (.forbid 1 4 1 (.system [[0],[1,14,4,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 4 3 (.system [[0],[1,14,15,16,4,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 4 4 (.system [[0],[1,14,15,16,17,4,3],[2],[5,6,7],[11],[13]]) (.forbid 1 4 5 (.system [[0],[1,14,15,16,17,18,4,3],[2],[5],[7],[11],[13]]) (.forbid 1 4 6 (.system [[0],[1,14,15,16,17,18,19,4,3],[2],[5],[7],[11],[13]]) (.forbid 1 6 1 (.system [[0],[1,14,6,5,4,3],[2],[7,8,9,10,11],[13]]) (.forbid 1 6 2 (.system [[0],[1,14,15,6,5],[2],[3],[7,8,9,10,11],[13]]) (.forbid 1 6 3 (.system [[0],[1,14,15,16,6,5],[2],[3],[7,8,9,10,11],[13]]) (.forbid 1 6 4 (.system [[0],[1,14,15,16,17,6,5,4,3],[2],[7],[11],[13]]) (.forbid 1 6 5 (.system [[0],[1,14,15,16,17,18,6,5],[2],[3],[7],[11],[13]]) (.forbid 1 6 6 (.system [[0],[1,14,15,16,17,18,19,6,5],[2],[3],[7],[11],[13]]) (.forbid 1 8 1 (.system [[0],[1,14,8,9,10,11],[2],[3,4,5,6,7],[13]]) (.forbid 1 10 1 (.system [[0],[1,14,10,9,8,7,6,5,4,3],[2],[11],[13]]) (.forbid 2 3 1 (.system [[0],[1],[2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 3 2 (.system [[0],[1],[2,14,15,3,4,5],[7,8,9,10,11],[13]]) (certificate_1589_part_2))))))))))))))))))))

noncomputable def certificate_1589_part_4 : FiniteCertificate := .forbid 0 4 3 (.system [[0,14,15,16,4,3],[1],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[1],[2],[5,6,7],[11],[13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3],[1],[2],[5],[7],[11],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[1],[2],[5],[7],[11],[13]]) (.forbid 0 6 1 (.system [[0,14,6,5,4,3],[1],[2],[7,8,9,10,11],[13]]) (.forbid 0 6 2 (.system [[0,14,15,6,5],[1],[2],[3],[7,8,9,10,11],[13]]) (.forbid 0 6 3 (.system [[0,14,15,16,6,5],[1],[2],[3],[7,8,9,10,11],[13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5,4,3],[1],[2],[7],[11],[13]]) (.forbid 0 6 5 (.system [[0,14,15,16,17,18,6,5],[1],[2],[3],[7],[11],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[1],[2],[3],[7],[11],[13]]) (.forbid 0 8 1 (.system [[0,14,8,9,10,11],[1],[2],[3,4,5,6,7],[13]]) (.forbid 0 10 1 (.system [[0,14,10,9,8,7,6,5,4,3],[1],[2],[11],[13]]) (.forbid 1 2 1 (.system [[0],[1,14,2],[3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2],[3,4,5],[7,8,9,10,11],[13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2],[3],[5],[7,8,9,10,11],[13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2],[3],[5],[7,8,9,10,11],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2],[3,4,5],[7],[11],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2],[3],[5],[7],[11],[13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,4,5,6,7,8,9,10,11,12,13],[2]]) (.forbid 1 3 2 (.system [[0],[1,14,15,3,4,5],[2],[7,8,9,10,11],[13]]) (certificate_1589_part_3))))))))))))))))))))

noncomputable def certificate_1589 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2],[3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[2],[3,4,5],[7,8,9,10,11],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[2],[3],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[2],[3],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[2],[3,4,5],[7],[11],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1],[2],[3],[5],[7],[11],[13]]) (.forbid 0 2 1 (.system [[0,14,2],[1],[3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2],[1],[3,4,5],[7,8,9,10,11],[13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2],[1],[3],[5],[7,8,9,10,11],[13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2],[1],[3],[5],[7,8,9,10,11],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2],[1],[3,4,5],[7],[11],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2],[1],[3],[5],[7],[11],[13]]) (.forbid 0 3 1 (.system [[0,14,3,4,5,6,7,8,9,10,11,12,13],[1],[2]]) (.forbid 0 3 2 (.system [[0,14,15,3,4,5],[1],[2],[7,8,9,10,11],[13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3],[1],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[1],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,4,5],[1],[2],[7],[11],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3],[1],[2],[5],[7],[11],[13]]) (.forbid 0 4 1 (.system [[0,14,4,3],[1],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[1],[2],[5],[7,8,9,10,11],[13]]) (certificate_1589_part_4))))))))))))))))))))

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

noncomputable def certificate_2788_part_4 : FiniteCertificate := .forbid 0 6 3 (.system [[0,17,18,19,6,5],[1],[3],[8,9,10,11],[12,13,14,15,16]]) (.forbid 0 6 4 (.system [[0,17,18,19,20,6,5],[1,2,3],[8],[11],[12,13,14,15,16]]) (.forbid 0 6 5 (.system [[0,17,18,19,20,21,6,5],[1],[3],[8],[11],[12,13,14,15,16]]) (.forbid 0 6 6 (.system [[0,17,18,19,20,21,22,6,5],[1],[3],[8,9,10,11],[12],[16]]) (.forbid 0 7 1 (.system [[0,17,7,6,5],[1,2,3],[8,9,10,11],[12,13,14,15,16]]) (.forbid 0 7 2 (.system [[0,17,18,7,6,5],[1],[3],[8,9,10,11],[12,13,14,15,16]]) (.forbid 0 7 3 (.system [[0,17,18,19,7,6,5],[1,2,3],[8],[11],[12,13,14,15,16]]) (.forbid 0 7 4 (.system [[0,17,18,19,20,7,6,5],[1],[3],[8],[11],[12,13,14,15,16]]) (.forbid 0 7 5 (.system [[0,17,18,19,20,21,7,6,5],[1],[3],[8,9,10,11],[12],[16]]) (.forbid 0 7 6 (.system [[0,17,18,19,20,21,22,7,6,5],[1,2,3],[8],[11],[12],[16]]) (.forbid 0 9 1 (.system [[0,17,9,10,11],[1,2,3],[5,6,7,8],[12,13,14,15,16]]) (.forbid 0 10 1 (.system [[0,17,10,9,8,7,6,5],[1,2,3],[11],[12,13,14,15,16]]) (.forbid 0 11 1 (.system [[0,17,11,10,9,8,7,6,5,4,3,2,1],[12,13,14,15,16]]) (.forbid 1 2 1 (.system [[0],[1,17,2,3],[5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 1 2 2 (.system [[0],[1,17,18,2,3,4,5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 1 2 3 (.system [[0],[1,17,18,19,2,3],[5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 1 2 4 (.system [[0],[1,17,18,19,20,2,3,4,5],[8],[11],[12,13,14,15,16]]) (.forbid 1 2 5 (.system [[0],[1,17,18,19,20,21,2,3],[5],[8],[11],[12,13,14,15,16]]) (.forbid 1 2 6 (.system [[0],[1,17,18,19,20,21,22,2,3],[5,6,7,8],[11],[12],[16]]) (.forbid 1 4 1 (.system [[0],[1,17,4,3],[5,6,7,8,9,10,11],[12,13,14,15,16]]) (certificate_2788_part_3))))))))))))))))))))

noncomputable def certificate_2788 : FiniteCertificate := .forbid 0 1 1 (.system [[0,17,1,2,3,4,5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 1 2 (.system [[0,17,18,1],[3],[5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 1 3 (.system [[0,17,18,19,1,2,3],[5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 0 1 4 (.system [[0,17,18,19,20,1],[3],[5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 0 1 5 (.system [[0,17,18,19,20,21,1,2,3],[5],[8],[11],[12,13,14,15,16]]) (.forbid 0 1 6 (.system [[0,17,18,19,20,21,22,1],[3],[5],[8],[11],[12,13,14,15,16]]) (.forbid 0 2 1 (.system [[0,17,2,1],[3],[5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 2 2 (.system [[0,17,18,2,1],[3,4,5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 0 2 3 (.system [[0,17,18,19,2,1],[3],[5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 0 2 4 (.system [[0,17,18,19,20,2,1],[3,4,5],[8],[11],[12,13,14,15,16]]) (.forbid 0 2 5 (.system [[0,17,18,19,20,21,2,1],[3],[5],[8],[11],[12,13,14,15,16]]) (.forbid 0 2 6 (.system [[0,17,18,19,20,21,22,2,1],[3],[5,6,7,8],[11],[12],[16]]) (.forbid 0 4 1 (.system [[0,17,4,3],[1],[5,6,7,8,9,10,11],[12,13,14,15,16]]) (.forbid 0 4 2 (.system [[0,17,18,4,3,2,1],[5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 0 4 3 (.system [[0,17,18,19,4,3],[1],[5,6,7,8],[11],[12,13,14,15,16]]) (.forbid 0 4 4 (.system [[0,17,18,19,20,4,3,2,1],[5],[8],[11],[12,13,14,15,16]]) (.forbid 0 4 5 (.system [[0,17,18,19,20,21,4,3],[1],[5],[8],[11],[12,13,14,15,16]]) (.forbid 0 4 6 (.system [[0,17,18,19,20,21,22,4,3],[1],[5,6,7,8],[11],[12],[16]]) (.forbid 0 6 1 (.system [[0,17,6,7,8,9,10,11],[1,2,3],[5],[12,13,14,15,16]]) (.forbid 0 6 2 (.system [[0,17,18,6,5],[1,2,3],[8,9,10,11],[12,13,14,15,16]]) (certificate_2788_part_4))))))))))))))))))))

end CycleClique

end OAI
end


