-- Prove2me | Definitions.Def_OAIQ107D005
-- name    : OAIQ107D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:38:59.04081+00:00
-- url     : https://prove2.me/theorems/3c0f06f4-048c-42fd-bbb0-61e5cdd2eef5
-- title:
--   Definitions bundle OAIQ107D005 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1142 declarations of OpenAI's Lean: 1142 definitions. The definitions and types are `OAI.CycleClique.certificate_2573_q`, `OAI.CycleClique.certificate_2574_edges`, `OAI.CycleClique.certificate_2574_q`, `OAI.CycleClique.certificate_2575_edges`, `OAI.CycleClique.certificate_2575_q`, `OAI.CycleClique.certificate_2576_edges`, `OAI.CycleClique.certificate_2576_q`, `OAI.CycleClique.certificate_2577_edges`, `OAI.CycleClique.certificate_2577_q`, `OAI.CycleClique.certificate_2578_edges`, `OAI.CycleClique.certificate_2578_q`, `OAI.CycleClique.certificate_2579_edges`, `OAI.CycleClique.certificate_2579_q`, `OAI.CycleClique.certificate_257_edges`, `OAI.CycleClique.certificate_257_q`, `OAI.CycleClique.certificate_2580_edges`, `OAI.CycleClique.certificate_2580_q`, `OAI.CycleClique.certificate_2581_edges`, `OAI.CycleClique.certificate_2581_q`, `OAI.CycleClique.certificate_2582_edges`, `OAI.CycleClique.certificate_2582_q`, `OAI.CycleClique.certificate_2583_edges`, `OAI.CycleClique.certificate_2583_q`, `OAI.CycleClique.certificate_2584_edges`, `OAI.CycleClique.certificate_2584_q`, `OAI.CycleClique.certificate_2585_edges`, `OAI.CycleClique.certificate_2585_q`, `OAI.CycleClique.certificate_2586_edges`, `OAI.CycleClique.certificate_2586_q`, `OAI.CycleClique.certificate_2587_edges`, `OAI.CycleClique.certificate_2587_q`, `OAI.CycleClique.certificate_2588_edges`, `OAI.CycleClique.certificate_2588_q`, `OAI.CycleClique.certificate_2589_edges`, `OAI.CycleClique.certificate_2589_q`, `OAI.CycleClique.certificate_258_edges`, `OAI.CycleClique.certificate_258_q`, `OAI.CycleClique.certificate_2590_edges`, `OAI.CycleClique.certificate_2590_q`, `OAI.CycleClique.certificate_2591_edges` and 1102 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates009`, `Ramsey_CycleClique_Certificates010`, `Ramsey_CycleClique_Certificates081`, `Ramsey_CycleClique_Certificates082`, `Ramsey_CycleClique_Certificates083`, `Ramsey_CycleClique_Certificates084`, `Ramsey_CycleClique_Certificates085`, `Ramsey_CycleClique_Certificates086`, `Ramsey_CycleClique_Certificates087`, `Ramsey_CycleClique_Certificates088`, `Ramsey_CycleClique_Certificates089`, `Ramsey_CycleClique_Certificates090`, `Ramsey_CycleClique_Certificates091`, `Ramsey_CycleClique_Certificates092`, `Ramsey_CycleClique_Certificates093`, `Ramsey_CycleClique_Certificates094`, `Ramsey_CycleClique_Certificates095`, `Ramsey_CycleClique_Certificates096`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D028`, `OAIQ107D040`, `OAIQ107D048`, `OAIQ107D078`, `OAIQ107D084`, `OAIQ107D085`, `OAIQ107D087`, `OAIQ107D089`, `OAIQ107D090`, `OAIQ107D094`, `OAIQ107D095`, `OAIQ107D096`, `OAIQ107D098` and `OAIQ107D099`; the proofs of `OAI.CycleClique.patterns_17_8_36_verified` and `OAI.CycleClique.patterns_17_8_42_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2_q : Finset ℕ := ([0,1,4] : List ℕ).toFinset

noncomputable def certificate_2_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(0,1),(0,4),(1,4)]

noncomputable def certificate_2_E : List (ℕ × ℕ) := certificate_2_edges

noncomputable def certificate_2_part_1_E : List (ℕ × ℕ) := certificate_2_E

noncomputable def certificate_2_part_3_E : List (ℕ × ℕ) := certificate_2_part_1_E

noncomputable def certificate_2_part_6_E : List (ℕ × ℕ) := certificate_2_part_3_E

noncomputable def certificate_25_q : Finset ℕ := ([0,1,6] : List ℕ).toFinset

noncomputable def certificate_25_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(0,1),(0,6),(1,6)]

noncomputable def certificate_25_E : List (ℕ × ℕ) := certificate_25_edges

noncomputable def certificate_25_part_1_E : List (ℕ × ℕ) := certificate_25_E

noncomputable def certificate_25_part_6_E : List (ℕ × ℕ) := certificate_25_part_1_E

noncomputable def certificate_25_part_8_E : List (ℕ × ℕ) := certificate_25_part_6_E

noncomputable def certificate_25_part_10_E : List (ℕ × ℕ) := certificate_25_part_8_E

noncomputable def certificate_25_part_16_E : List (ℕ × ℕ) := certificate_25_part_10_E

noncomputable def certificate_26_q : Finset ℕ := ([0,2,4] : List ℕ).toFinset
noncomputable def certificate_26_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(0,2),(0,4),(2,4)]

noncomputable def certificate_27_q : Finset ℕ := ([0,2,5] : List ℕ).toFinset
noncomputable def certificate_27_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,2),(0,5),(2,5)]

noncomputable def certificate_28_q : Finset ℕ := ([0,2,6] : List ℕ).toFinset

noncomputable def certificate_28_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,2),(0,6),(2,6)]

noncomputable def certificate_28_E : List (ℕ × ℕ) := certificate_28_edges

noncomputable def certificate_28_part_1_E : List (ℕ × ℕ) := certificate_28_E

noncomputable def certificate_28_part_2_E : List (ℕ × ℕ) := certificate_28_part_1_E

noncomputable def certificate_28_part_3_E : List (ℕ × ℕ) := certificate_28_part_2_E

noncomputable def certificate_28_part_6_E : List (ℕ × ℕ) := certificate_28_part_3_E

noncomputable def certificate_29_q : Finset ℕ := ([0,3,6] : List ℕ).toFinset

noncomputable def certificate_29_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,3),(0,6),(3,6)]

noncomputable def certificate_29_E : List (ℕ × ℕ) := certificate_29_edges

noncomputable def certificate_29_part_1_E : List (ℕ × ℕ) := certificate_29_E

noncomputable def certificate_29_part_2_E : List (ℕ × ℕ) := certificate_29_part_1_E

noncomputable def certificate_29_part_3_E : List (ℕ × ℕ) := certificate_29_part_2_E

noncomputable def certificate_29_part_4_E : List (ℕ × ℕ) := certificate_29_part_3_E

noncomputable def certificate_29_part_5_E : List (ℕ × ℕ) := certificate_29_part_4_E

noncomputable def certificate_29_part_7_E : List (ℕ × ℕ) := certificate_29_part_5_E

noncomputable def certificate_29_part_8_E : List (ℕ × ℕ) := certificate_29_part_7_E

noncomputable def certificate_29_part_9_E : List (ℕ × ℕ) := certificate_29_part_8_E

noncomputable def certificate_30_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset

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

noncomputable def certificate_257_q : Finset ℕ := ([0,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_257_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(0,2),(0,3),(0,5),(0,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_258_q : Finset ℕ := ([0,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_258_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,3),(0,5),(0,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_259_q : Finset ℕ := ([0,2,3,5,9] : List ℕ).toFinset
noncomputable def certificate_259_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,9),(2,3),(2,5),(2,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_260_q : Finset ℕ := ([0,2,3,5,10] : List ℕ).toFinset
noncomputable def certificate_260_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,10),(2,3),(2,5),(2,10),(3,5),(3,10),(5,10)]

noncomputable def certificate_261_q : Finset ℕ := ([0,2,3,6,9] : List ℕ).toFinset
noncomputable def certificate_261_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,6),(0,9),(2,3),(2,6),(2,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_262_q : Finset ℕ := ([0,2,3,6,10] : List ℕ).toFinset
noncomputable def certificate_262_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,6),(0,10),(2,3),(2,6),(2,10),(3,6),(3,10),(6,10)]

noncomputable def certificate_263_q : Finset ℕ := ([0,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_263_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(0,2),(0,4),(0,5),(0,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_264_q : Finset ℕ := ([0,2,4,5,9] : List ℕ).toFinset
noncomputable def certificate_264_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,5),(0,9),(2,4),(2,5),(2,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_265_q : Finset ℕ := ([0,2,4,5,10] : List ℕ).toFinset
noncomputable def certificate_265_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,5),(0,10),(2,4),(2,5),(2,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_266_q : Finset ℕ := ([0,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_266_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,4),(0,6),(0,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_267_q : Finset ℕ := ([0,2,4,6,9] : List ℕ).toFinset
noncomputable def certificate_267_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,6),(0,9),(2,4),(2,6),(2,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_268_q : Finset ℕ := ([0,2,4,6,10] : List ℕ).toFinset
noncomputable def certificate_268_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,10),(2,4),(2,6),(2,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_269_q : Finset ℕ := ([0,2,4,7,9] : List ℕ).toFinset
noncomputable def certificate_269_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,7),(0,9),(2,4),(2,7),(2,9),(4,7),(4,9),(7,9)]

noncomputable def certificate_270_q : Finset ℕ := ([0,2,4,7,10] : List ℕ).toFinset
noncomputable def certificate_270_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,7),(0,10),(2,4),(2,7),(2,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_271_q : Finset ℕ := ([0,2,4,8,10] : List ℕ).toFinset
noncomputable def certificate_271_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,8),(0,10),(2,4),(2,8),(2,10),(4,8),(4,10),(8,10)]

noncomputable def certificate_272_q : Finset ℕ := ([0,2,5,6,9] : List ℕ).toFinset
noncomputable def certificate_272_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,2),(0,5),(0,6),(0,9),(2,5),(2,6),(2,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_273_q : Finset ℕ := ([0,2,5,6,10] : List ℕ).toFinset
noncomputable def certificate_273_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,5),(0,6),(0,10),(2,5),(2,6),(2,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_274_q : Finset ℕ := ([0,2,5,7,10] : List ℕ).toFinset
noncomputable def certificate_274_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,5),(0,7),(0,10),(2,5),(2,7),(2,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_275_q : Finset ℕ := ([0,2,5,8,10] : List ℕ).toFinset
noncomputable def certificate_275_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,5),(0,8),(0,10),(2,5),(2,8),(2,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_276_q : Finset ℕ := ([0,2,6,7,10] : List ℕ).toFinset
noncomputable def certificate_276_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,6),(0,7),(0,10),(2,6),(2,7),(2,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_277_q : Finset ℕ := ([0,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_277_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,3),(0,4),(0,7),(0,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_278_q : Finset ℕ := ([0,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_278_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,3),(0,5),(0,7),(0,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_279_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_279_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_280_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_280_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_281_q : Finset ℕ := ([0,1,2,3,4,7] : List ℕ).toFinset
noncomputable def certificate_281_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,3),(1,4),(1,7),(2,3),(2,4),(2,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_282_q : Finset ℕ := ([0,1,2,3,4,8] : List ℕ).toFinset
noncomputable def certificate_282_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,8),(1,2),(1,3),(1,4),(1,8),(2,3),(2,4),(2,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_283_q : Finset ℕ := ([0,1,2,3,4,9] : List ℕ).toFinset
noncomputable def certificate_283_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,9),(1,2),(1,3),(1,4),(1,9),(2,3),(2,4),(2,9),(3,4),(3,9),(4,9)]

noncomputable def certificate_284_q : Finset ℕ := ([0,1,2,3,4,10] : List ℕ).toFinset

noncomputable def certificate_284_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,10),(1,2),(1,3),(1,4),(1,10),(2,3),(2,4),(2,10),(3,4),(3,10),(4,10)]

noncomputable def certificate_284_E : List (ℕ × ℕ) := certificate_284_edges

noncomputable def certificate_284_part_1_E : List (ℕ × ℕ) := certificate_284_E

noncomputable def certificate_284_part_2_E : List (ℕ × ℕ) := certificate_284_part_1_E

noncomputable def certificate_284_part_3_E : List (ℕ × ℕ) := certificate_284_part_2_E

noncomputable def certificate_284_part_4_E : List (ℕ × ℕ) := certificate_284_part_3_E

noncomputable def certificate_284_part_5_E : List (ℕ × ℕ) := certificate_284_part_4_E

noncomputable def certificate_284_part_7_E : List (ℕ × ℕ) := certificate_284_part_5_E

noncomputable def certificate_284_part_8_E : List (ℕ × ℕ) := certificate_284_part_7_E

noncomputable def certificate_284_part_18_E : List (ℕ × ℕ) := certificate_284_part_8_E

noncomputable def certificate_284_part_19_E : List (ℕ × ℕ) := certificate_284_part_18_E

noncomputable def certificate_284_part_22_E : List (ℕ × ℕ) := certificate_284_part_19_E

noncomputable def certificate_284_part_32_E : List (ℕ × ℕ) := certificate_284_part_22_E

noncomputable def certificate_284_part_43_E : List (ℕ × ℕ) := certificate_284_part_32_E

noncomputable def certificate_284_part_45_E : List (ℕ × ℕ) := certificate_284_part_43_E

noncomputable def certificate_284_part_49_E : List (ℕ × ℕ) := certificate_284_part_45_E

noncomputable def certificate_284_part_51_E : List (ℕ × ℕ) := certificate_284_part_49_E

noncomputable def certificate_285_q : Finset ℕ := ([0,1,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_285_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,5),(0,7),(1,2),(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_286_q : Finset ℕ := ([0,1,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_286_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,8),(1,2),(1,3),(1,5),(1,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_287_q : Finset ℕ := ([0,1,2,3,5,9] : List ℕ).toFinset
noncomputable def certificate_287_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,9),(1,2),(1,3),(1,5),(1,9),(2,3),(2,5),(2,9),(3,5),(3,9),(5,9)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_288_q : Finset ℕ := ([0,1,2,3,5,10] : List ℕ).toFinset
noncomputable def certificate_288_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,10),(1,2),(1,3),(1,5),(1,10),(2,3),(2,5),(2,10),(3,5),(3,10),(5,10)]

noncomputable def certificate_289_q : Finset ℕ := ([0,1,2,3,6,9] : List ℕ).toFinset
noncomputable def certificate_289_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,6),(0,9),(1,2),(1,3),(1,6),(1,9),(2,3),(2,6),(2,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_290_q : Finset ℕ := ([0,1,2,3,6,10] : List ℕ).toFinset
noncomputable def certificate_290_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,10),(1,2),(1,3),(1,6),(1,10),(2,3),(2,6),(2,10),(3,6),(3,10),(6,10)]

noncomputable def certificate_291_q : Finset ℕ := ([0,1,2,4,5,7] : List ℕ).toFinset
noncomputable def certificate_291_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(0,1),(0,2),(0,4),(0,5),(0,7),(1,2),(1,4),(1,5),(1,7),(2,4),(2,5),(2,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_292_q : Finset ℕ := ([0,1,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_292_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,5),(0,8),(1,2),(1,4),(1,5),(1,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_293_q : Finset ℕ := ([0,1,2,4,5,9] : List ℕ).toFinset
noncomputable def certificate_293_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,9),(1,2),(1,4),(1,5),(1,9),(2,4),(2,5),(2,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_294_q : Finset ℕ := ([0,1,2,4,5,10] : List ℕ).toFinset
noncomputable def certificate_294_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,10),(1,2),(1,4),(1,5),(1,10),(2,4),(2,5),(2,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_295_q : Finset ℕ := ([0,1,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_295_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,6),(0,8),(1,2),(1,4),(1,6),(1,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_296_q : Finset ℕ := ([0,1,2,4,6,9] : List ℕ).toFinset
noncomputable def certificate_296_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,6),(0,9),(1,2),(1,4),(1,6),(1,9),(2,4),(2,6),(2,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_297_q : Finset ℕ := ([0,1,2,4,6,10] : List ℕ).toFinset
noncomputable def certificate_297_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,10),(1,2),(1,4),(1,6),(1,10),(2,4),(2,6),(2,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_298_q : Finset ℕ := ([0,1,2,4,7,9] : List ℕ).toFinset
noncomputable def certificate_298_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,7),(0,9),(1,2),(1,4),(1,7),(1,9),(2,4),(2,7),(2,9),(4,7),(4,9),(7,9)]

noncomputable def certificate_299_q : Finset ℕ := ([0,1,2,4,7,10] : List ℕ).toFinset
noncomputable def certificate_299_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,7),(0,10),(1,2),(1,4),(1,7),(1,10),(2,4),(2,7),(2,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_300_q : Finset ℕ := ([0,1,2,4,8,10] : List ℕ).toFinset
noncomputable def certificate_300_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,8),(0,10),(1,2),(1,4),(1,8),(1,10),(2,4),(2,8),(2,10),(4,8),(4,10),(8,10)]

noncomputable def certificate_301_q : Finset ℕ := ([0,1,2,5,6,9] : List ℕ).toFinset
noncomputable def certificate_301_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,5),(0,6),(0,9),(1,2),(1,5),(1,6),(1,9),(2,5),(2,6),(2,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_302_q : Finset ℕ := ([0,1,2,5,6,10] : List ℕ).toFinset
noncomputable def certificate_302_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,6),(0,10),(1,2),(1,5),(1,6),(1,10),(2,5),(2,6),(2,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_303_q : Finset ℕ := ([0,1,2,5,7,10] : List ℕ).toFinset
noncomputable def certificate_303_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,7),(0,10),(1,2),(1,5),(1,7),(1,10),(2,5),(2,7),(2,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_304_q : Finset ℕ := ([0,1,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_304_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,6),(0,8),(1,3),(1,4),(1,6),(1,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_305_q : Finset ℕ := ([0,1,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_305_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,9),(1,3),(1,4),(1,6),(1,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates081
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2573_q : Finset ℕ := ([0,1,2,4,7,10,12,16] : List ℕ).toFinset

noncomputable def certificate_2574_q : Finset ℕ := ([0,1,2,4,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2574_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,10),(0,13),(0,15),(1,2),(1,4),(1,7),(1,10),(1,13),(1,15),(2,4),(2,7),(2,10),(2,13),(2,15),(4,7),(4,10),(4,13),(4,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2575_q : Finset ℕ := ([0,1,2,4,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2575_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,10),(0,13),(0,16),(1,2),(1,4),(1,7),(1,10),(1,13),(1,16),(2,4),(2,7),(2,10),(2,13),(2,16),(4,7),(4,10),(4,13),(4,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2576_q : Finset ℕ := ([0,1,2,4,7,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2576_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,10),(0,14),(0,16),(1,2),(1,4),(1,7),(1,10),(1,14),(1,16),(2,4),(2,7),(2,10),(2,14),(2,16),(4,7),(4,10),(4,14),(4,16),(7,10),(7,14),(7,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2577_q : Finset ℕ := ([0,1,2,4,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2577_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,11),(0,12),(0,15),(1,2),(1,4),(1,7),(1,11),(1,12),(1,15),(2,4),(2,7),(2,11),(2,12),(2,15),(4,7),(4,11),(4,12),(4,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2578_q : Finset ℕ := ([0,1,2,4,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2578_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,11),(0,12),(0,16),(1,2),(1,4),(1,7),(1,11),(1,12),(1,16),(2,4),(2,7),(2,11),(2,12),(2,16),(4,7),(4,11),(4,12),(4,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2579_q : Finset ℕ := ([0,1,2,4,7,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2579_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,11),(0,13),(0,16),(1,2),(1,4),(1,7),(1,11),(1,13),(1,16),(2,4),(2,7),(2,11),(2,13),(2,16),(4,7),(4,11),(4,13),(4,16),(7,11),(7,13),(7,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2580_q : Finset ℕ := ([0,1,2,4,7,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2580_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,11),(0,14),(0,16),(1,2),(1,4),(1,7),(1,11),(1,14),(1,16),(2,4),(2,7),(2,11),(2,14),(2,16),(4,7),(4,11),(4,14),(4,16),(7,11),(7,14),(7,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2581_q : Finset ℕ := ([0,1,2,4,7,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2581_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,12),(0,13),(0,16),(1,2),(1,4),(1,7),(1,12),(1,13),(1,16),(2,4),(2,7),(2,12),(2,13),(2,16),(4,7),(4,12),(4,13),(4,16),(7,12),(7,13),(7,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2582_q : Finset ℕ := ([0,1,2,4,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2582_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,9),(0,11),(0,15),(1,2),(1,4),(1,8),(1,9),(1,11),(1,15),(2,4),(2,8),(2,9),(2,11),(2,15),(4,8),(4,9),(4,11),(4,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2583_q : Finset ℕ := ([0,1,2,4,8,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2583_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,9),(0,11),(0,16),(1,2),(1,4),(1,8),(1,9),(1,11),(1,16),(2,4),(2,8),(2,9),(2,11),(2,16),(4,8),(4,9),(4,11),(4,16),(8,9),(8,11),(8,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2584_q : Finset ℕ := ([0,1,2,4,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2584_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,9),(0,12),(0,15),(1,2),(1,4),(1,8),(1,9),(1,12),(1,15),(2,4),(2,8),(2,9),(2,12),(2,15),(4,8),(4,9),(4,12),(4,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2585_q : Finset ℕ := ([0,1,2,4,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2585_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,9),(0,12),(0,16),(1,2),(1,4),(1,8),(1,9),(1,12),(1,16),(2,4),(2,8),(2,9),(2,12),(2,16),(4,8),(4,9),(4,12),(4,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2586_q : Finset ℕ := ([0,1,2,4,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2586_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,10),(0,11),(0,14),(1,2),(1,4),(1,8),(1,10),(1,11),(1,14),(2,4),(2,8),(2,10),(2,11),(2,14),(4,8),(4,10),(4,11),(4,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2587_q : Finset ℕ := ([0,1,2,4,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2587_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,10),(0,11),(0,15),(1,2),(1,4),(1,8),(1,10),(1,11),(1,15),(2,4),(2,8),(2,10),(2,11),(2,15),(4,8),(4,10),(4,11),(4,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2588_q : Finset ℕ := ([0,1,2,4,8,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2588_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,10),(0,11),(0,16),(1,2),(1,4),(1,8),(1,10),(1,11),(1,16),(2,4),(2,8),(2,10),(2,11),(2,16),(4,8),(4,10),(4,11),(4,16),(8,10),(8,11),(8,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2589_q : Finset ℕ := ([0,1,2,4,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2589_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,10),(0,12),(0,15),(1,2),(1,4),(1,8),(1,10),(1,12),(1,15),(2,4),(2,8),(2,10),(2,12),(2,15),(4,8),(4,10),(4,12),(4,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2590_q : Finset ℕ := ([0,1,2,4,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2590_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,10),(0,12),(0,16),(1,2),(1,4),(1,8),(1,10),(1,12),(1,16),(2,4),(2,8),(2,10),(2,12),(2,16),(4,8),(4,10),(4,12),(4,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2591_q : Finset ℕ := ([0,1,2,4,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2591_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,10),(0,13),(0,16),(1,2),(1,4),(1,8),(1,10),(1,13),(1,16),(2,4),(2,8),(2,10),(2,13),(2,16),(4,8),(4,10),(4,13),(4,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2592_q : Finset ℕ := ([0,1,2,4,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2592_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,10),(0,14),(0,16),(1,2),(1,4),(1,8),(1,10),(1,14),(1,16),(2,4),(2,8),(2,10),(2,14),(2,16),(4,8),(4,10),(4,14),(4,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2593_q : Finset ℕ := ([0,1,2,4,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2593_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,11),(0,12),(0,15),(1,2),(1,4),(1,8),(1,11),(1,12),(1,15),(2,4),(2,8),(2,11),(2,12),(2,15),(4,8),(4,11),(4,12),(4,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2594_q : Finset ℕ := ([0,1,2,4,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2594_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,11),(0,12),(0,16),(1,2),(1,4),(1,8),(1,11),(1,12),(1,16),(2,4),(2,8),(2,11),(2,12),(2,16),(4,8),(4,11),(4,12),(4,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2595_q : Finset ℕ := ([0,1,2,4,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2595_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,11),(0,13),(0,16),(1,2),(1,4),(1,8),(1,11),(1,13),(1,16),(2,4),(2,8),(2,11),(2,13),(2,16),(4,8),(4,11),(4,13),(4,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2596_q : Finset ℕ := ([0,1,2,4,8,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2596_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,8),(0,12),(0,13),(0,16),(1,2),(1,4),(1,8),(1,12),(1,13),(1,16),(2,4),(2,8),(2,12),(2,13),(2,16),(4,8),(4,12),(4,13),(4,16),(8,12),(8,13),(8,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2597_q : Finset ℕ := ([0,1,2,4,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2597_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,9),(0,10),(0,13),(0,16),(1,2),(1,4),(1,9),(1,10),(1,13),(1,16),(2,4),(2,9),(2,10),(2,13),(2,16),(4,9),(4,10),(4,13),(4,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2598_q : Finset ℕ := ([0,1,2,4,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2598_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,9),(0,11),(0,12),(0,15),(1,2),(1,4),(1,9),(1,11),(1,12),(1,15),(2,4),(2,9),(2,11),(2,12),(2,15),(4,9),(4,11),(4,12),(4,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2599_q : Finset ℕ := ([0,1,2,4,9,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2599_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,9),(0,11),(0,12),(0,16),(1,2),(1,4),(1,9),(1,11),(1,12),(1,16),(2,4),(2,9),(2,11),(2,12),(2,16),(4,9),(4,11),(4,12),(4,16),(9,11),(9,12),(9,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2600_q : Finset ℕ := ([0,1,2,4,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2600_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,9),(0,11),(0,13),(0,16),(1,2),(1,4),(1,9),(1,11),(1,13),(1,16),(2,4),(2,9),(2,11),(2,13),(2,16),(4,9),(4,11),(4,13),(4,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2601_q : Finset ℕ := ([0,1,2,4,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2601_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,9),(0,12),(0,13),(0,16),(1,2),(1,4),(1,9),(1,12),(1,13),(1,16),(2,4),(2,9),(2,12),(2,13),(2,16),(4,9),(4,12),(4,13),(4,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2602_q : Finset ℕ := ([0,1,2,4,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2602_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,10),(0,12),(0,13),(0,16),(1,2),(1,4),(1,10),(1,12),(1,13),(1,16),(2,4),(2,10),(2,12),(2,13),(2,16),(4,10),(4,12),(4,13),(4,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2603_q : Finset ℕ := ([0,1,2,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2603_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(1,2),(1,5),(1,6),(1,9),(1,10),(1,13),(2,5),(2,6),(2,9),(2,10),(2,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2604_q : Finset ℕ := ([0,1,2,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2604_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,14),(1,2),(1,5),(1,6),(1,9),(1,10),(1,14),(2,5),(2,6),(2,9),(2,10),(2,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2605_q : Finset ℕ := ([0,1,2,5,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2605_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,15),(1,2),(1,5),(1,6),(1,9),(1,10),(1,15),(2,5),(2,6),(2,9),(2,10),(2,15),(5,6),(5,9),(5,10),(5,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2606_q : Finset ℕ := ([0,1,2,5,6,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2606_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,16),(1,2),(1,5),(1,6),(1,9),(1,10),(1,16),(2,5),(2,6),(2,9),(2,10),(2,16),(5,6),(5,9),(5,10),(5,16),(6,9),(6,10),(6,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2607_q : Finset ℕ := ([0,1,2,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2607_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,11),(0,14),(1,2),(1,5),(1,6),(1,9),(1,11),(1,14),(2,5),(2,6),(2,9),(2,11),(2,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2608_q : Finset ℕ := ([0,1,2,5,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2608_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,9),(0,11),(0,15),(1,2),(1,5),(1,6),(1,9),(1,11),(1,15),(2,5),(2,6),(2,9),(2,11),(2,15),(5,6),(5,9),(5,11),(5,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2609_q : Finset ℕ := ([0,1,2,5,6,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2609_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,6),(0,9),(0,11),(0,16),(1,2),(1,5),(1,6),(1,9),(1,11),(1,16),(2,5),(2,6),(2,9),(2,11),(2,16),(5,6),(5,9),(5,11),(5,16),(6,9),(6,11),(6,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2610_q : Finset ℕ := ([0,1,2,5,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2610_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,9),(0,12),(0,15),(1,2),(1,5),(1,6),(1,9),(1,12),(1,15),(2,5),(2,6),(2,9),(2,12),(2,15),(5,6),(5,9),(5,12),(5,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2611_q : Finset ℕ := ([0,1,2,5,6,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2611_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,6),(0,9),(0,12),(0,16),(1,2),(1,5),(1,6),(1,9),(1,12),(1,16),(2,5),(2,6),(2,9),(2,12),(2,16),(5,6),(5,9),(5,12),(5,16),(6,9),(6,12),(6,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2612_q : Finset ℕ := ([0,1,2,5,6,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2612_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,6),(0,9),(0,13),(0,16),(1,2),(1,5),(1,6),(1,9),(1,13),(1,16),(2,5),(2,6),(2,9),(2,13),(2,16),(5,6),(5,9),(5,13),(5,16),(6,9),(6,13),(6,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2613_q : Finset ℕ := ([0,1,2,5,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2613_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,10),(0,11),(0,15),(1,2),(1,5),(1,6),(1,10),(1,11),(1,15),(2,5),(2,6),(2,10),(2,11),(2,15),(5,6),(5,10),(5,11),(5,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2614_q : Finset ℕ := ([0,1,2,5,6,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2614_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,6),(0,10),(0,11),(0,16),(1,2),(1,5),(1,6),(1,10),(1,11),(1,16),(2,5),(2,6),(2,10),(2,11),(2,16),(5,6),(5,10),(5,11),(5,16),(6,10),(6,11),(6,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2615_q : Finset ℕ := ([0,1,2,5,6,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2615_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,6),(0,10),(0,12),(0,16),(1,2),(1,5),(1,6),(1,10),(1,12),(1,16),(2,5),(2,6),(2,10),(2,12),(2,16),(5,6),(5,10),(5,12),(5,16),(6,10),(6,12),(6,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2616_q : Finset ℕ := ([0,1,2,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2616_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,7),(0,9),(0,11),(0,14),(1,2),(1,5),(1,7),(1,9),(1,11),(1,14),(2,5),(2,7),(2,9),(2,11),(2,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2617_q : Finset ℕ := ([0,1,2,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2617_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,9),(0,11),(0,15),(1,2),(1,5),(1,7),(1,9),(1,11),(1,15),(2,5),(2,7),(2,9),(2,11),(2,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2618_q : Finset ℕ := ([0,1,2,5,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2618_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,9),(0,11),(0,16),(1,2),(1,5),(1,7),(1,9),(1,11),(1,16),(2,5),(2,7),(2,9),(2,11),(2,16),(5,7),(5,9),(5,11),(5,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2619_q : Finset ℕ := ([0,1,2,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2619_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,9),(0,12),(0,15),(1,2),(1,5),(1,7),(1,9),(1,12),(1,15),(2,5),(2,7),(2,9),(2,12),(2,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2620_q : Finset ℕ := ([0,1,2,5,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2620_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,9),(0,12),(0,16),(1,2),(1,5),(1,7),(1,9),(1,12),(1,16),(2,5),(2,7),(2,9),(2,12),(2,16),(5,7),(5,9),(5,12),(5,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2621_q : Finset ℕ := ([0,1,2,5,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2621_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,9),(0,13),(0,16),(1,2),(1,5),(1,7),(1,9),(1,13),(1,16),(2,5),(2,7),(2,9),(2,13),(2,16),(5,7),(5,9),(5,13),(5,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2622_q : Finset ℕ := ([0,1,2,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2622_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,10),(0,11),(0,15),(1,2),(1,5),(1,7),(1,10),(1,11),(1,15),(2,5),(2,7),(2,10),(2,11),(2,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2623_q : Finset ℕ := ([0,1,2,5,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2623_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,10),(0,11),(0,16),(1,2),(1,5),(1,7),(1,10),(1,11),(1,16),(2,5),(2,7),(2,10),(2,11),(2,16),(5,7),(5,10),(5,11),(5,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates083
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2624_q : Finset ℕ := ([0,1,2,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2624_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,10),(0,12),(0,15),(1,2),(1,5),(1,7),(1,10),(1,12),(1,15),(2,5),(2,7),(2,10),(2,12),(2,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2625_q : Finset ℕ := ([0,1,2,5,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2625_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,10),(0,12),(0,16),(1,2),(1,5),(1,7),(1,10),(1,12),(1,16),(2,5),(2,7),(2,10),(2,12),(2,16),(5,7),(5,10),(5,12),(5,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2626_q : Finset ℕ := ([0,1,2,5,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2626_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,10),(0,13),(0,16),(1,2),(1,5),(1,7),(1,10),(1,13),(1,16),(2,5),(2,7),(2,10),(2,13),(2,16),(5,7),(5,10),(5,13),(5,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2627_q : Finset ℕ := ([0,1,2,5,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2627_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,11),(0,12),(0,16),(1,2),(1,5),(1,7),(1,11),(1,12),(1,16),(2,5),(2,7),(2,11),(2,12),(2,16),(5,7),(5,11),(5,12),(5,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2628_q : Finset ℕ := ([0,1,2,5,7,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2628_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,7),(0,11),(0,13),(0,16),(1,2),(1,5),(1,7),(1,11),(1,13),(1,16),(2,5),(2,7),(2,11),(2,13),(2,16),(5,7),(5,11),(5,13),(5,16),(7,11),(7,13),(7,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2629_q : Finset ℕ := ([0,1,2,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2629_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,8),(0,9),(0,12),(0,15),(1,2),(1,5),(1,8),(1,9),(1,12),(1,15),(2,5),(2,8),(2,9),(2,12),(2,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2630_q : Finset ℕ := ([0,1,2,5,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2630_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,8),(0,9),(0,12),(0,16),(1,2),(1,5),(1,8),(1,9),(1,12),(1,16),(2,5),(2,8),(2,9),(2,12),(2,16),(5,8),(5,9),(5,12),(5,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2631_q : Finset ℕ := ([0,1,2,5,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2631_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,8),(0,10),(0,12),(0,16),(1,2),(1,5),(1,8),(1,10),(1,12),(1,16),(2,5),(2,8),(2,10),(2,12),(2,16),(5,8),(5,10),(5,12),(5,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2632_q : Finset ℕ := ([0,1,2,5,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2632_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,8),(0,10),(0,13),(0,16),(1,2),(1,5),(1,8),(1,10),(1,13),(1,16),(2,5),(2,8),(2,10),(2,13),(2,16),(5,8),(5,10),(5,13),(5,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2633_q : Finset ℕ := ([0,1,2,5,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2633_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,5),(0,8),(0,11),(0,12),(0,16),(1,2),(1,5),(1,8),(1,11),(1,12),(1,16),(2,5),(2,8),(2,11),(2,12),(2,16),(5,8),(5,11),(5,12),(5,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2634_q : Finset ℕ := ([0,1,2,6,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2634_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,6),(0,7),(0,11),(0,12),(0,16),(1,2),(1,6),(1,7),(1,11),(1,12),(1,16),(2,6),(2,7),(2,11),(2,12),(2,16),(6,7),(6,11),(6,12),(6,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2635_q : Finset ℕ := ([0,1,2,6,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2635_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,6),(0,8),(0,10),(0,12),(0,16),(1,2),(1,6),(1,8),(1,10),(1,12),(1,16),(2,6),(2,8),(2,10),(2,12),(2,16),(6,8),(6,10),(6,12),(6,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2636_q : Finset ℕ := ([0,1,3,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_2636_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,11),(1,3),(1,4),(1,6),(1,7),(1,9),(1,11),(3,4),(3,6),(3,7),(3,9),(3,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_2637_q : Finset ℕ := ([0,1,3,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_2637_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,12),(1,3),(1,4),(1,6),(1,7),(1,9),(1,12),(3,4),(3,6),(3,7),(3,9),(3,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_2638_q : Finset ℕ := ([0,1,3,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_2638_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,13),(1,3),(1,4),(1,6),(1,7),(1,9),(1,13),(3,4),(3,6),(3,7),(3,9),(3,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_2639_q : Finset ℕ := ([0,1,3,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_2639_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,14),(1,3),(1,4),(1,6),(1,7),(1,9),(1,14),(3,4),(3,6),(3,7),(3,9),(3,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_2640_q : Finset ℕ := ([0,1,3,4,6,7,9,15] : List ℕ).toFinset
noncomputable def certificate_2640_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,15),(1,3),(1,4),(1,6),(1,7),(1,9),(1,15),(3,4),(3,6),(3,7),(3,9),(3,15),(4,6),(4,7),(4,9),(4,15),(6,7),(6,9),(6,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_2641_q : Finset ℕ := ([0,1,3,4,6,7,9,16] : List ℕ).toFinset
noncomputable def certificate_2641_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,16),(1,3),(1,4),(1,6),(1,7),(1,9),(1,16),(3,4),(3,6),(3,7),(3,9),(3,16),(4,6),(4,7),(4,9),(4,16),(6,7),(6,9),(6,16),(7,9),(7,16),(9,16)]

noncomputable def certificate_2642_q : Finset ℕ := ([0,1,3,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2642_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,13),(1,3),(1,4),(1,6),(1,7),(1,10),(1,13),(3,4),(3,6),(3,7),(3,10),(3,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_2643_q : Finset ℕ := ([0,1,3,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2643_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,14),(1,3),(1,4),(1,6),(1,7),(1,10),(1,14),(3,4),(3,6),(3,7),(3,10),(3,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2644_q : Finset ℕ := ([0,1,3,4,6,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2644_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,15),(1,3),(1,4),(1,6),(1,7),(1,10),(1,15),(3,4),(3,6),(3,7),(3,10),(3,15),(4,6),(4,7),(4,10),(4,15),(6,7),(6,10),(6,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2645_q : Finset ℕ := ([0,1,3,4,6,7,10,16] : List ℕ).toFinset
noncomputable def certificate_2645_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,16),(1,3),(1,4),(1,6),(1,7),(1,10),(1,16),(3,4),(3,6),(3,7),(3,10),(3,16),(4,6),(4,7),(4,10),(4,16),(6,7),(6,10),(6,16),(7,10),(7,16),(10,16)]

noncomputable def certificate_2646_q : Finset ℕ := ([0,1,3,4,6,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2646_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(0,15),(1,3),(1,4),(1,6),(1,7),(1,11),(1,15),(3,4),(3,6),(3,7),(3,11),(3,15),(4,6),(4,7),(4,11),(4,15),(6,7),(6,11),(6,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2647_q : Finset ℕ := ([0,1,3,4,6,7,11,16] : List ℕ).toFinset
noncomputable def certificate_2647_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(0,16),(1,3),(1,4),(1,6),(1,7),(1,11),(1,16),(3,4),(3,6),(3,7),(3,11),(3,16),(4,6),(4,7),(4,11),(4,16),(6,7),(6,11),(6,16),(7,11),(7,16),(11,16)]

noncomputable def certificate_2648_q : Finset ℕ := ([0,1,3,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2648_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,12),(1,3),(1,4),(1,6),(1,8),(1,9),(1,12),(3,4),(3,6),(3,8),(3,9),(3,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2649_q : Finset ℕ := ([0,1,3,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2649_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,13),(1,3),(1,4),(1,6),(1,8),(1,9),(1,13),(3,4),(3,6),(3,8),(3,9),(3,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2650_q : Finset ℕ := ([0,1,3,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2650_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,14),(1,3),(1,4),(1,6),(1,8),(1,9),(1,14),(3,4),(3,6),(3,8),(3,9),(3,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2651_q : Finset ℕ := ([0,1,3,4,6,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2651_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,15),(1,3),(1,4),(1,6),(1,8),(1,9),(1,15),(3,4),(3,6),(3,8),(3,9),(3,15),(4,6),(4,8),(4,9),(4,15),(6,8),(6,9),(6,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2652_q : Finset ℕ := ([0,1,3,4,6,8,9,16] : List ℕ).toFinset
noncomputable def certificate_2652_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,16),(1,3),(1,4),(1,6),(1,8),(1,9),(1,16),(3,4),(3,6),(3,8),(3,9),(3,16),(4,6),(4,8),(4,9),(4,16),(6,8),(6,9),(6,16),(8,9),(8,16),(9,16)]

noncomputable def certificate_2653_q : Finset ℕ := ([0,1,3,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2653_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,12),(1,3),(1,4),(1,6),(1,8),(1,10),(1,12),(3,4),(3,6),(3,8),(3,10),(3,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2654_q : Finset ℕ := ([0,1,3,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2654_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,13),(1,3),(1,4),(1,6),(1,8),(1,10),(1,13),(3,4),(3,6),(3,8),(3,10),(3,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2655_q : Finset ℕ := ([0,1,3,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2655_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,14),(1,3),(1,4),(1,6),(1,8),(1,10),(1,14),(3,4),(3,6),(3,8),(3,10),(3,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates084
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2656_q : Finset ℕ := ([0,1,3,4,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2656_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,15),(1,3),(1,4),(1,6),(1,8),(1,10),(1,15),(3,4),(3,6),(3,8),(3,10),(3,15),(4,6),(4,8),(4,10),(4,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2657_q : Finset ℕ := ([0,1,3,4,6,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2657_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,16),(1,3),(1,4),(1,6),(1,8),(1,10),(1,16),(3,4),(3,6),(3,8),(3,10),(3,16),(4,6),(4,8),(4,10),(4,16),(6,8),(6,10),(6,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2658_q : Finset ℕ := ([0,1,3,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2658_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,13),(1,3),(1,4),(1,6),(1,8),(1,11),(1,13),(3,4),(3,6),(3,8),(3,11),(3,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2659_q : Finset ℕ := ([0,1,3,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2659_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,14),(1,3),(1,4),(1,6),(1,8),(1,11),(1,14),(3,4),(3,6),(3,8),(3,11),(3,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2660_q : Finset ℕ := ([0,1,3,4,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2660_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,15),(1,3),(1,4),(1,6),(1,8),(1,11),(1,15),(3,4),(3,6),(3,8),(3,11),(3,15),(4,6),(4,8),(4,11),(4,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2661_q : Finset ℕ := ([0,1,3,4,6,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2661_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,16),(1,3),(1,4),(1,6),(1,8),(1,11),(1,16),(3,4),(3,6),(3,8),(3,11),(3,16),(4,6),(4,8),(4,11),(4,16),(6,8),(6,11),(6,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2662_q : Finset ℕ := ([0,1,3,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2662_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(0,14),(1,3),(1,4),(1,6),(1,8),(1,12),(1,14),(3,4),(3,6),(3,8),(3,12),(3,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2663_q : Finset ℕ := ([0,1,3,4,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2663_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(0,15),(1,3),(1,4),(1,6),(1,8),(1,12),(1,15),(3,4),(3,6),(3,8),(3,12),(3,15),(4,6),(4,8),(4,12),(4,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2664_q : Finset ℕ := ([0,1,3,4,6,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2664_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(0,16),(1,3),(1,4),(1,6),(1,8),(1,12),(1,16),(3,4),(3,6),(3,8),(3,12),(3,16),(4,6),(4,8),(4,12),(4,16),(6,8),(6,12),(6,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2665_q : Finset ℕ := ([0,1,3,4,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2665_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,13),(0,15),(1,3),(1,4),(1,6),(1,8),(1,13),(1,15),(3,4),(3,6),(3,8),(3,13),(3,15),(4,6),(4,8),(4,13),(4,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2666_q : Finset ℕ := ([0,1,3,4,6,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2666_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,8),(0,13),(0,16),(1,3),(1,4),(1,6),(1,8),(1,13),(1,16),(3,4),(3,6),(3,8),(3,13),(3,16),(4,6),(4,8),(4,13),(4,16),(6,8),(6,13),(6,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2667_q : Finset ℕ := ([0,1,3,4,6,8,14,16] : List ℕ).toFinset
noncomputable def certificate_2667_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,8),(0,14),(0,16),(1,3),(1,4),(1,6),(1,8),(1,14),(1,16),(3,4),(3,6),(3,8),(3,14),(3,16),(4,6),(4,8),(4,14),(4,16),(6,8),(6,14),(6,16),(8,14),(8,16),(14,16)]

noncomputable def certificate_2668_q : Finset ℕ := ([0,1,3,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2668_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,13),(1,3),(1,4),(1,6),(1,9),(1,10),(1,13),(3,4),(3,6),(3,9),(3,10),(3,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2669_q : Finset ℕ := ([0,1,3,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2669_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,14),(1,3),(1,4),(1,6),(1,9),(1,10),(1,14),(3,4),(3,6),(3,9),(3,10),(3,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2670_q : Finset ℕ := ([0,1,3,4,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2670_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,15),(1,3),(1,4),(1,6),(1,9),(1,10),(1,15),(3,4),(3,6),(3,9),(3,10),(3,15),(4,6),(4,9),(4,10),(4,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2671_q : Finset ℕ := ([0,1,3,4,6,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2671_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,16),(1,3),(1,4),(1,6),(1,9),(1,10),(1,16),(3,4),(3,6),(3,9),(3,10),(3,16),(4,6),(4,9),(4,10),(4,16),(6,9),(6,10),(6,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2672_q : Finset ℕ := ([0,1,3,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2672_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(0,14),(1,3),(1,4),(1,6),(1,9),(1,11),(1,14),(3,4),(3,6),(3,9),(3,11),(3,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2673_q : Finset ℕ := ([0,1,3,4,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2673_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(0,15),(1,3),(1,4),(1,6),(1,9),(1,11),(1,15),(3,4),(3,6),(3,9),(3,11),(3,15),(4,6),(4,9),(4,11),(4,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2674_q : Finset ℕ := ([0,1,3,4,6,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2674_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(0,16),(1,3),(1,4),(1,6),(1,9),(1,11),(1,16),(3,4),(3,6),(3,9),(3,11),(3,16),(4,6),(4,9),(4,11),(4,16),(6,9),(6,11),(6,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2675_q : Finset ℕ := ([0,1,3,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2675_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(0,14),(1,3),(1,4),(1,6),(1,9),(1,12),(1,14),(3,4),(3,6),(3,9),(3,12),(3,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2676_q : Finset ℕ := ([0,1,3,4,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2676_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(0,15),(1,3),(1,4),(1,6),(1,9),(1,12),(1,15),(3,4),(3,6),(3,9),(3,12),(3,15),(4,6),(4,9),(4,12),(4,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2677_q : Finset ℕ := ([0,1,3,4,6,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2677_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(0,16),(1,3),(1,4),(1,6),(1,9),(1,12),(1,16),(3,4),(3,6),(3,9),(3,12),(3,16),(4,6),(4,9),(4,12),(4,16),(6,9),(6,12),(6,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2678_q : Finset ℕ := ([0,1,3,4,6,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2678_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,13),(0,15),(1,3),(1,4),(1,6),(1,9),(1,13),(1,15),(3,4),(3,6),(3,9),(3,13),(3,15),(4,6),(4,9),(4,13),(4,15),(6,9),(6,13),(6,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2679_q : Finset ℕ := ([0,1,3,4,6,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2679_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,9),(0,13),(0,16),(1,3),(1,4),(1,6),(1,9),(1,13),(1,16),(3,4),(3,6),(3,9),(3,13),(3,16),(4,6),(4,9),(4,13),(4,16),(6,9),(6,13),(6,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2680_q : Finset ℕ := ([0,1,3,4,6,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2680_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,9),(0,14),(0,16),(1,3),(1,4),(1,6),(1,9),(1,14),(1,16),(3,4),(3,6),(3,9),(3,14),(3,16),(4,6),(4,9),(4,14),(4,16),(6,9),(6,14),(6,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2681_q : Finset ℕ := ([0,1,3,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2681_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,10),(0,11),(0,14),(1,3),(1,4),(1,6),(1,10),(1,11),(1,14),(3,4),(3,6),(3,10),(3,11),(3,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2682_q : Finset ℕ := ([0,1,3,4,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2682_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,10),(0,11),(0,15),(1,3),(1,4),(1,6),(1,10),(1,11),(1,15),(3,4),(3,6),(3,10),(3,11),(3,15),(4,6),(4,10),(4,11),(4,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2683_q : Finset ℕ := ([0,1,3,4,6,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2683_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,10),(0,11),(0,16),(1,3),(1,4),(1,6),(1,10),(1,11),(1,16),(3,4),(3,6),(3,10),(3,11),(3,16),(4,6),(4,10),(4,11),(4,16),(6,10),(6,11),(6,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2684_q : Finset ℕ := ([0,1,3,4,6,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2684_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,10),(0,12),(0,15),(1,3),(1,4),(1,6),(1,10),(1,12),(1,15),(3,4),(3,6),(3,10),(3,12),(3,15),(4,6),(4,10),(4,12),(4,15),(6,10),(6,12),(6,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2685_q : Finset ℕ := ([0,1,3,4,6,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2685_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,10),(0,12),(0,16),(1,3),(1,4),(1,6),(1,10),(1,12),(1,16),(3,4),(3,6),(3,10),(3,12),(3,16),(4,6),(4,10),(4,12),(4,16),(6,10),(6,12),(6,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2686_q : Finset ℕ := ([0,1,3,4,6,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2686_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,10),(0,13),(0,16),(1,3),(1,4),(1,6),(1,10),(1,13),(1,16),(3,4),(3,6),(3,10),(3,13),(3,16),(4,6),(4,10),(4,13),(4,16),(6,10),(6,13),(6,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2687_q : Finset ℕ := ([0,1,3,4,6,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2687_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,10),(0,14),(0,16),(1,3),(1,4),(1,6),(1,10),(1,14),(1,16),(3,4),(3,6),(3,10),(3,14),(3,16),(4,6),(4,10),(4,14),(4,16),(6,10),(6,14),(6,16),(10,14),(10,16),(14,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates085
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2688_q : Finset ℕ := ([0,1,3,4,6,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2688_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,11),(0,12),(0,15),(1,3),(1,4),(1,6),(1,11),(1,12),(1,15),(3,4),(3,6),(3,11),(3,12),(3,15),(4,6),(4,11),(4,12),(4,15),(6,11),(6,12),(6,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2689_q : Finset ℕ := ([0,1,3,4,6,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2689_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,11),(0,12),(0,16),(1,3),(1,4),(1,6),(1,11),(1,12),(1,16),(3,4),(3,6),(3,11),(3,12),(3,16),(4,6),(4,11),(4,12),(4,16),(6,11),(6,12),(6,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2690_q : Finset ℕ := ([0,1,3,4,6,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2690_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,11),(0,13),(0,16),(1,3),(1,4),(1,6),(1,11),(1,13),(1,16),(3,4),(3,6),(3,11),(3,13),(3,16),(4,6),(4,11),(4,13),(4,16),(6,11),(6,13),(6,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2691_q : Finset ℕ := ([0,1,3,4,6,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2691_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,6),(0,12),(0,13),(0,16),(1,3),(1,4),(1,6),(1,12),(1,13),(1,16),(3,4),(3,6),(3,12),(3,13),(3,16),(4,6),(4,12),(4,13),(4,16),(6,12),(6,13),(6,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2692_q : Finset ℕ := ([0,1,3,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2692_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(0,14),(1,3),(1,4),(1,7),(1,8),(1,11),(1,14),(3,4),(3,7),(3,8),(3,11),(3,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2693_q : Finset ℕ := ([0,1,3,4,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2693_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(0,15),(1,3),(1,4),(1,7),(1,8),(1,11),(1,15),(3,4),(3,7),(3,8),(3,11),(3,15),(4,7),(4,8),(4,11),(4,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2694_q : Finset ℕ := ([0,1,3,4,7,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2694_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(0,16),(1,3),(1,4),(1,7),(1,8),(1,11),(1,16),(3,4),(3,7),(3,8),(3,11),(3,16),(4,7),(4,8),(4,11),(4,16),(7,8),(7,11),(7,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2695_q : Finset ℕ := ([0,1,3,4,7,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2695_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,8),(0,12),(0,16),(1,3),(1,4),(1,7),(1,8),(1,12),(1,16),(3,4),(3,7),(3,8),(3,12),(3,16),(4,7),(4,8),(4,12),(4,16),(7,8),(7,12),(7,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2696_q : Finset ℕ := ([0,1,3,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2696_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,9),(0,11),(0,14),(1,3),(1,4),(1,7),(1,9),(1,11),(1,14),(3,4),(3,7),(3,9),(3,11),(3,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2697_q : Finset ℕ := ([0,1,3,4,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2697_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,9),(0,11),(0,15),(1,3),(1,4),(1,7),(1,9),(1,11),(1,15),(3,4),(3,7),(3,9),(3,11),(3,15),(4,7),(4,9),(4,11),(4,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2698_q : Finset ℕ := ([0,1,3,4,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2698_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,9),(0,11),(0,16),(1,3),(1,4),(1,7),(1,9),(1,11),(1,16),(3,4),(3,7),(3,9),(3,11),(3,16),(4,7),(4,9),(4,11),(4,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2699_q : Finset ℕ := ([0,1,3,4,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2699_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,9),(0,12),(0,15),(1,3),(1,4),(1,7),(1,9),(1,12),(1,15),(3,4),(3,7),(3,9),(3,12),(3,15),(4,7),(4,9),(4,12),(4,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2700_q : Finset ℕ := ([0,1,3,4,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2700_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,9),(0,12),(0,16),(1,3),(1,4),(1,7),(1,9),(1,12),(1,16),(3,4),(3,7),(3,9),(3,12),(3,16),(4,7),(4,9),(4,12),(4,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2701_q : Finset ℕ := ([0,1,3,4,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2701_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,9),(0,13),(0,16),(1,3),(1,4),(1,7),(1,9),(1,13),(1,16),(3,4),(3,7),(3,9),(3,13),(3,16),(4,7),(4,9),(4,13),(4,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2702_q : Finset ℕ := ([0,1,3,4,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2702_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,10),(0,11),(0,15),(1,3),(1,4),(1,7),(1,10),(1,11),(1,15),(3,4),(3,7),(3,10),(3,11),(3,15),(4,7),(4,10),(4,11),(4,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2703_q : Finset ℕ := ([0,1,3,4,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2703_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,10),(0,11),(0,16),(1,3),(1,4),(1,7),(1,10),(1,11),(1,16),(3,4),(3,7),(3,10),(3,11),(3,16),(4,7),(4,10),(4,11),(4,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2704_q : Finset ℕ := ([0,1,3,4,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2704_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,10),(0,12),(0,16),(1,3),(1,4),(1,7),(1,10),(1,12),(1,16),(3,4),(3,7),(3,10),(3,12),(3,16),(4,7),(4,10),(4,12),(4,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2705_q : Finset ℕ := ([0,1,3,4,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2705_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,10),(0,13),(0,16),(1,3),(1,4),(1,7),(1,10),(1,13),(1,16),(3,4),(3,7),(3,10),(3,13),(3,16),(4,7),(4,10),(4,13),(4,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2706_q : Finset ℕ := ([0,1,3,4,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2706_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,7),(0,11),(0,12),(0,16),(1,3),(1,4),(1,7),(1,11),(1,12),(1,16),(3,4),(3,7),(3,11),(3,12),(3,16),(4,7),(4,11),(4,12),(4,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2707_q : Finset ℕ := ([0,1,3,4,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2707_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,4),(0,8),(0,10),(0,12),(0,16),(1,3),(1,4),(1,8),(1,10),(1,12),(1,16),(3,4),(3,8),(3,10),(3,12),(3,16),(4,8),(4,10),(4,12),(4,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2708_q : Finset ℕ := ([0,1,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2708_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(1,3),(1,5),(1,6),(1,8),(1,10),(1,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2709_q : Finset ℕ := ([0,1,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2709_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(1,3),(1,5),(1,6),(1,8),(1,10),(1,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2710_q : Finset ℕ := ([0,1,3,5,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2710_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,14),(1,3),(1,5),(1,6),(1,8),(1,10),(1,14),(3,5),(3,6),(3,8),(3,10),(3,14),(5,6),(5,8),(5,10),(5,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2711_q : Finset ℕ := ([0,1,3,5,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2711_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,15),(1,3),(1,5),(1,6),(1,8),(1,10),(1,15),(3,5),(3,6),(3,8),(3,10),(3,15),(5,6),(5,8),(5,10),(5,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2712_q : Finset ℕ := ([0,1,3,5,6,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2712_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,16),(1,3),(1,5),(1,6),(1,8),(1,10),(1,16),(3,5),(3,6),(3,8),(3,10),(3,16),(5,6),(5,8),(5,10),(5,16),(6,8),(6,10),(6,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2713_q : Finset ℕ := ([0,1,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2713_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(1,3),(1,5),(1,6),(1,8),(1,11),(1,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2714_q : Finset ℕ := ([0,1,3,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2714_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,14),(1,3),(1,5),(1,6),(1,8),(1,11),(1,14),(3,5),(3,6),(3,8),(3,11),(3,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2715_q : Finset ℕ := ([0,1,3,5,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2715_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,15),(1,3),(1,5),(1,6),(1,8),(1,11),(1,15),(3,5),(3,6),(3,8),(3,11),(3,15),(5,6),(5,8),(5,11),(5,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2716_q : Finset ℕ := ([0,1,3,5,6,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2716_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,16),(1,3),(1,5),(1,6),(1,8),(1,11),(1,16),(3,5),(3,6),(3,8),(3,11),(3,16),(5,6),(5,8),(5,11),(5,16),(6,8),(6,11),(6,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2717_q : Finset ℕ := ([0,1,3,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2717_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(0,14),(1,3),(1,5),(1,6),(1,8),(1,12),(1,14),(3,5),(3,6),(3,8),(3,12),(3,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2718_q : Finset ℕ := ([0,1,3,5,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2718_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(0,15),(1,3),(1,5),(1,6),(1,8),(1,12),(1,15),(3,5),(3,6),(3,8),(3,12),(3,15),(5,6),(5,8),(5,12),(5,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2719_q : Finset ℕ := ([0,1,3,5,6,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2719_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(0,16),(1,3),(1,5),(1,6),(1,8),(1,12),(1,16),(3,5),(3,6),(3,8),(3,12),(3,16),(5,6),(5,8),(5,12),(5,16),(6,8),(6,12),(6,16),(8,12),(8,16),(12,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates086
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2720_q : Finset ℕ := ([0,1,3,5,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2720_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,13),(0,15),(1,3),(1,5),(1,6),(1,8),(1,13),(1,15),(3,5),(3,6),(3,8),(3,13),(3,15),(5,6),(5,8),(5,13),(5,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2721_q : Finset ℕ := ([0,1,3,5,6,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2721_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,8),(0,13),(0,16),(1,3),(1,5),(1,6),(1,8),(1,13),(1,16),(3,5),(3,6),(3,8),(3,13),(3,16),(5,6),(5,8),(5,13),(5,16),(6,8),(6,13),(6,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2722_q : Finset ℕ := ([0,1,3,5,6,8,14,16] : List ℕ).toFinset
noncomputable def certificate_2722_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,8),(0,14),(0,16),(1,3),(1,5),(1,6),(1,8),(1,14),(1,16),(3,5),(3,6),(3,8),(3,14),(3,16),(5,6),(5,8),(5,14),(5,16),(6,8),(6,14),(6,16),(8,14),(8,16),(14,16)]

noncomputable def certificate_2723_q : Finset ℕ := ([0,1,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2723_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(1,3),(1,5),(1,6),(1,9),(1,10),(1,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2724_q : Finset ℕ := ([0,1,3,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2724_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,14),(1,3),(1,5),(1,6),(1,9),(1,10),(1,14),(3,5),(3,6),(3,9),(3,10),(3,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2725_q : Finset ℕ := ([0,1,3,5,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2725_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,15),(1,3),(1,5),(1,6),(1,9),(1,10),(1,15),(3,5),(3,6),(3,9),(3,10),(3,15),(5,6),(5,9),(5,10),(5,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2726_q : Finset ℕ := ([0,1,3,5,6,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2726_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,16),(1,3),(1,5),(1,6),(1,9),(1,10),(1,16),(3,5),(3,6),(3,9),(3,10),(3,16),(5,6),(5,9),(5,10),(5,16),(6,9),(6,10),(6,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2727_q : Finset ℕ := ([0,1,3,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2727_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,11),(0,14),(1,3),(1,5),(1,6),(1,9),(1,11),(1,14),(3,5),(3,6),(3,9),(3,11),(3,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2728_q : Finset ℕ := ([0,1,3,5,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2728_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,9),(0,11),(0,15),(1,3),(1,5),(1,6),(1,9),(1,11),(1,15),(3,5),(3,6),(3,9),(3,11),(3,15),(5,6),(5,9),(5,11),(5,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2729_q : Finset ℕ := ([0,1,3,5,6,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2729_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,9),(0,11),(0,16),(1,3),(1,5),(1,6),(1,9),(1,11),(1,16),(3,5),(3,6),(3,9),(3,11),(3,16),(5,6),(5,9),(5,11),(5,16),(6,9),(6,11),(6,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2730_q : Finset ℕ := ([0,1,3,5,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2730_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,9),(0,12),(0,15),(1,3),(1,5),(1,6),(1,9),(1,12),(1,15),(3,5),(3,6),(3,9),(3,12),(3,15),(5,6),(5,9),(5,12),(5,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2731_q : Finset ℕ := ([0,1,3,5,6,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2731_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,9),(0,12),(0,16),(1,3),(1,5),(1,6),(1,9),(1,12),(1,16),(3,5),(3,6),(3,9),(3,12),(3,16),(5,6),(5,9),(5,12),(5,16),(6,9),(6,12),(6,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2732_q : Finset ℕ := ([0,1,3,5,6,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2732_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,9),(0,13),(0,16),(1,3),(1,5),(1,6),(1,9),(1,13),(1,16),(3,5),(3,6),(3,9),(3,13),(3,16),(5,6),(5,9),(5,13),(5,16),(6,9),(6,13),(6,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2733_q : Finset ℕ := ([0,1,3,5,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2733_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,10),(0,11),(0,15),(1,3),(1,5),(1,6),(1,10),(1,11),(1,15),(3,5),(3,6),(3,10),(3,11),(3,15),(5,6),(5,10),(5,11),(5,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2734_q : Finset ℕ := ([0,1,3,5,6,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2734_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,10),(0,11),(0,16),(1,3),(1,5),(1,6),(1,10),(1,11),(1,16),(3,5),(3,6),(3,10),(3,11),(3,16),(5,6),(5,10),(5,11),(5,16),(6,10),(6,11),(6,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2735_q : Finset ℕ := ([0,1,3,5,6,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2735_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,6),(0,10),(0,12),(0,16),(1,3),(1,5),(1,6),(1,10),(1,12),(1,16),(3,5),(3,6),(3,10),(3,12),(3,16),(5,6),(5,10),(5,12),(5,16),(6,10),(6,12),(6,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2736_q : Finset ℕ := ([0,1,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2736_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(1,3),(1,5),(1,7),(1,8),(1,10),(1,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2737_q : Finset ℕ := ([0,1,3,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2737_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,14),(1,3),(1,5),(1,7),(1,8),(1,10),(1,14),(3,5),(3,7),(3,8),(3,10),(3,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2738_q : Finset ℕ := ([0,1,3,5,7,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2738_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,15),(1,3),(1,5),(1,7),(1,8),(1,10),(1,15),(3,5),(3,7),(3,8),(3,10),(3,15),(5,7),(5,8),(5,10),(5,15),(7,8),(7,10),(7,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2739_q : Finset ℕ := ([0,1,3,5,7,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2739_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,16),(1,3),(1,5),(1,7),(1,8),(1,10),(1,16),(3,5),(3,7),(3,8),(3,10),(3,16),(5,7),(5,8),(5,10),(5,16),(7,8),(7,10),(7,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2740_q : Finset ℕ := ([0,1,3,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2740_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(0,14),(1,3),(1,5),(1,7),(1,8),(1,11),(1,14),(3,5),(3,7),(3,8),(3,11),(3,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2741_q : Finset ℕ := ([0,1,3,5,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2741_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(0,15),(1,3),(1,5),(1,7),(1,8),(1,11),(1,15),(3,5),(3,7),(3,8),(3,11),(3,15),(5,7),(5,8),(5,11),(5,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2742_q : Finset ℕ := ([0,1,3,5,7,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2742_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(0,16),(1,3),(1,5),(1,7),(1,8),(1,11),(1,16),(3,5),(3,7),(3,8),(3,11),(3,16),(5,7),(5,8),(5,11),(5,16),(7,8),(7,11),(7,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2743_q : Finset ℕ := ([0,1,3,5,7,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2743_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,8),(0,12),(0,16),(1,3),(1,5),(1,7),(1,8),(1,12),(1,16),(3,5),(3,7),(3,8),(3,12),(3,16),(5,7),(5,8),(5,12),(5,16),(7,8),(7,12),(7,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2744_q : Finset ℕ := ([0,1,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2744_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(1,3),(1,5),(1,7),(1,9),(1,10),(1,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2745_q : Finset ℕ := ([0,1,3,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2745_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,14),(1,3),(1,5),(1,7),(1,9),(1,10),(1,14),(3,5),(3,7),(3,9),(3,10),(3,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2746_q : Finset ℕ := ([0,1,3,5,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2746_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,15),(1,3),(1,5),(1,7),(1,9),(1,10),(1,15),(3,5),(3,7),(3,9),(3,10),(3,15),(5,7),(5,9),(5,10),(5,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2747_q : Finset ℕ := ([0,1,3,5,7,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2747_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,16),(1,3),(1,5),(1,7),(1,9),(1,10),(1,16),(3,5),(3,7),(3,9),(3,10),(3,16),(5,7),(5,9),(5,10),(5,16),(7,9),(7,10),(7,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2748_q : Finset ℕ := ([0,1,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2748_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(1,3),(1,5),(1,7),(1,9),(1,11),(1,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2749_q : Finset ℕ := ([0,1,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2749_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(1,3),(1,5),(1,7),(1,9),(1,11),(1,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2750_q : Finset ℕ := ([0,1,3,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2750_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,15),(1,3),(1,5),(1,7),(1,9),(1,11),(1,15),(3,5),(3,7),(3,9),(3,11),(3,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2751_q : Finset ℕ := ([0,1,3,5,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2751_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,16),(1,3),(1,5),(1,7),(1,9),(1,11),(1,16),(3,5),(3,7),(3,9),(3,11),(3,16),(5,7),(5,9),(5,11),(5,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates087
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2752_q : Finset ℕ := ([0,1,3,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2752_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(0,14),(1,3),(1,5),(1,7),(1,9),(1,12),(1,14),(3,5),(3,7),(3,9),(3,12),(3,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2753_q : Finset ℕ := ([0,1,3,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2753_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(0,15),(1,3),(1,5),(1,7),(1,9),(1,12),(1,15),(3,5),(3,7),(3,9),(3,12),(3,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2754_q : Finset ℕ := ([0,1,3,5,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2754_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(0,16),(1,3),(1,5),(1,7),(1,9),(1,12),(1,16),(3,5),(3,7),(3,9),(3,12),(3,16),(5,7),(5,9),(5,12),(5,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2755_q : Finset ℕ := ([0,1,3,5,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2755_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,13),(0,15),(1,3),(1,5),(1,7),(1,9),(1,13),(1,15),(3,5),(3,7),(3,9),(3,13),(3,15),(5,7),(5,9),(5,13),(5,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2756_q : Finset ℕ := ([0,1,3,5,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2756_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,9),(0,13),(0,16),(1,3),(1,5),(1,7),(1,9),(1,13),(1,16),(3,5),(3,7),(3,9),(3,13),(3,16),(5,7),(5,9),(5,13),(5,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2757_q : Finset ℕ := ([0,1,3,5,7,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2757_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,9),(0,14),(0,16),(1,3),(1,5),(1,7),(1,9),(1,14),(1,16),(3,5),(3,7),(3,9),(3,14),(3,16),(5,7),(5,9),(5,14),(5,16),(7,9),(7,14),(7,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2758_q : Finset ℕ := ([0,1,3,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2758_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,11),(0,14),(1,3),(1,5),(1,7),(1,10),(1,11),(1,14),(3,5),(3,7),(3,10),(3,11),(3,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2759_q : Finset ℕ := ([0,1,3,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2759_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,10),(0,11),(0,15),(1,3),(1,5),(1,7),(1,10),(1,11),(1,15),(3,5),(3,7),(3,10),(3,11),(3,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2760_q : Finset ℕ := ([0,1,3,5,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2760_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,10),(0,11),(0,16),(1,3),(1,5),(1,7),(1,10),(1,11),(1,16),(3,5),(3,7),(3,10),(3,11),(3,16),(5,7),(5,10),(5,11),(5,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2761_q : Finset ℕ := ([0,1,3,5,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_2761_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(0,14),(1,3),(1,5),(1,7),(1,10),(1,12),(1,14),(3,5),(3,7),(3,10),(3,12),(3,14),(5,7),(5,10),(5,12),(5,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_2762_q : Finset ℕ := ([0,1,3,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2762_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(0,15),(1,3),(1,5),(1,7),(1,10),(1,12),(1,15),(3,5),(3,7),(3,10),(3,12),(3,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2763_q : Finset ℕ := ([0,1,3,5,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2763_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(0,16),(1,3),(1,5),(1,7),(1,10),(1,12),(1,16),(3,5),(3,7),(3,10),(3,12),(3,16),(5,7),(5,10),(5,12),(5,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2764_q : Finset ℕ := ([0,1,3,5,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2764_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,10),(0,13),(0,15),(1,3),(1,5),(1,7),(1,10),(1,13),(1,15),(3,5),(3,7),(3,10),(3,13),(3,15),(5,7),(5,10),(5,13),(5,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2765_q : Finset ℕ := ([0,1,3,5,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2765_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,10),(0,13),(0,16),(1,3),(1,5),(1,7),(1,10),(1,13),(1,16),(3,5),(3,7),(3,10),(3,13),(3,16),(5,7),(5,10),(5,13),(5,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2766_q : Finset ℕ := ([0,1,3,5,7,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2766_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,10),(0,14),(0,16),(1,3),(1,5),(1,7),(1,10),(1,14),(1,16),(3,5),(3,7),(3,10),(3,14),(3,16),(5,7),(5,10),(5,14),(5,16),(7,10),(7,14),(7,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2767_q : Finset ℕ := ([0,1,3,5,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2767_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,11),(0,12),(0,15),(1,3),(1,5),(1,7),(1,11),(1,12),(1,15),(3,5),(3,7),(3,11),(3,12),(3,15),(5,7),(5,11),(5,12),(5,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2768_q : Finset ℕ := ([0,1,3,5,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2768_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,11),(0,12),(0,16),(1,3),(1,5),(1,7),(1,11),(1,12),(1,16),(3,5),(3,7),(3,11),(3,12),(3,16),(5,7),(5,11),(5,12),(5,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2769_q : Finset ℕ := ([0,1,3,5,7,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2769_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,11),(0,13),(0,15),(1,3),(1,5),(1,7),(1,11),(1,13),(1,15),(3,5),(3,7),(3,11),(3,13),(3,15),(5,7),(5,11),(5,13),(5,15),(7,11),(7,13),(7,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2770_q : Finset ℕ := ([0,1,3,5,7,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2770_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,11),(0,13),(0,16),(1,3),(1,5),(1,7),(1,11),(1,13),(1,16),(3,5),(3,7),(3,11),(3,13),(3,16),(5,7),(5,11),(5,13),(5,16),(7,11),(7,13),(7,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2771_q : Finset ℕ := ([0,1,3,5,7,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2771_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,11),(0,14),(0,16),(1,3),(1,5),(1,7),(1,11),(1,14),(1,16),(3,5),(3,7),(3,11),(3,14),(3,16),(5,7),(5,11),(5,14),(5,16),(7,11),(7,14),(7,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2772_q : Finset ℕ := ([0,1,3,5,7,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2772_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,12),(0,13),(0,16),(1,3),(1,5),(1,7),(1,12),(1,13),(1,16),(3,5),(3,7),(3,12),(3,13),(3,16),(5,7),(5,12),(5,13),(5,16),(7,12),(7,13),(7,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2773_q : Finset ℕ := ([0,1,3,5,7,12,14,16] : List ℕ).toFinset
noncomputable def certificate_2773_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,7),(0,12),(0,14),(0,16),(1,3),(1,5),(1,7),(1,12),(1,14),(1,16),(3,5),(3,7),(3,12),(3,14),(3,16),(5,7),(5,12),(5,14),(5,16),(7,12),(7,14),(7,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_2774_q : Finset ℕ := ([0,1,3,5,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2774_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,9),(0,11),(0,14),(1,3),(1,5),(1,8),(1,9),(1,11),(1,14),(3,5),(3,8),(3,9),(3,11),(3,14),(5,8),(5,9),(5,11),(5,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2775_q : Finset ℕ := ([0,1,3,5,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2775_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,9),(0,11),(0,15),(1,3),(1,5),(1,8),(1,9),(1,11),(1,15),(3,5),(3,8),(3,9),(3,11),(3,15),(5,8),(5,9),(5,11),(5,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2776_q : Finset ℕ := ([0,1,3,5,8,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2776_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,9),(0,11),(0,16),(1,3),(1,5),(1,8),(1,9),(1,11),(1,16),(3,5),(3,8),(3,9),(3,11),(3,16),(5,8),(5,9),(5,11),(5,16),(8,9),(8,11),(8,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2777_q : Finset ℕ := ([0,1,3,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2777_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,9),(0,12),(0,15),(1,3),(1,5),(1,8),(1,9),(1,12),(1,15),(3,5),(3,8),(3,9),(3,12),(3,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2778_q : Finset ℕ := ([0,1,3,5,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2778_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,9),(0,12),(0,16),(1,3),(1,5),(1,8),(1,9),(1,12),(1,16),(3,5),(3,8),(3,9),(3,12),(3,16),(5,8),(5,9),(5,12),(5,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2779_q : Finset ℕ := ([0,1,3,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2779_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,10),(0,11),(0,14),(1,3),(1,5),(1,8),(1,10),(1,11),(1,14),(3,5),(3,8),(3,10),(3,11),(3,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2780_q : Finset ℕ := ([0,1,3,5,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2780_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,10),(0,11),(0,15),(1,3),(1,5),(1,8),(1,10),(1,11),(1,15),(3,5),(3,8),(3,10),(3,11),(3,15),(5,8),(5,10),(5,11),(5,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2781_q : Finset ℕ := ([0,1,3,5,8,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2781_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,10),(0,11),(0,16),(1,3),(1,5),(1,8),(1,10),(1,11),(1,16),(3,5),(3,8),(3,10),(3,11),(3,16),(5,8),(5,10),(5,11),(5,16),(8,10),(8,11),(8,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2782_q : Finset ℕ := ([0,1,3,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2782_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,10),(0,12),(0,15),(1,3),(1,5),(1,8),(1,10),(1,12),(1,15),(3,5),(3,8),(3,10),(3,12),(3,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2783_q : Finset ℕ := ([0,1,3,5,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2783_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,10),(0,12),(0,16),(1,3),(1,5),(1,8),(1,10),(1,12),(1,16),(3,5),(3,8),(3,10),(3,12),(3,16),(5,8),(5,10),(5,12),(5,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

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

noncomputable def certificate_2784_q : Finset ℕ := ([0,1,3,5,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2784_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,10),(0,13),(0,15),(1,3),(1,5),(1,8),(1,10),(1,13),(1,15),(3,5),(3,8),(3,10),(3,13),(3,15),(5,8),(5,10),(5,13),(5,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2785_q : Finset ℕ := ([0,1,3,5,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2785_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,10),(0,13),(0,16),(1,3),(1,5),(1,8),(1,10),(1,13),(1,16),(3,5),(3,8),(3,10),(3,13),(3,16),(5,8),(5,10),(5,13),(5,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2786_q : Finset ℕ := ([0,1,3,5,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2786_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,10),(0,14),(0,16),(1,3),(1,5),(1,8),(1,10),(1,14),(1,16),(3,5),(3,8),(3,10),(3,14),(3,16),(5,8),(5,10),(5,14),(5,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2787_q : Finset ℕ := ([0,1,3,5,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2787_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,11),(0,12),(0,15),(1,3),(1,5),(1,8),(1,11),(1,12),(1,15),(3,5),(3,8),(3,11),(3,12),(3,15),(5,8),(5,11),(5,12),(5,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2788_q : Finset ℕ := ([0,1,3,5,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2788_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,11),(0,12),(0,16),(1,3),(1,5),(1,8),(1,11),(1,12),(1,16),(3,5),(3,8),(3,11),(3,12),(3,16),(5,8),(5,11),(5,12),(5,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2789_q : Finset ℕ := ([0,1,3,5,8,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2789_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,11),(0,13),(0,15),(1,3),(1,5),(1,8),(1,11),(1,13),(1,15),(3,5),(3,8),(3,11),(3,13),(3,15),(5,8),(5,11),(5,13),(5,15),(8,11),(8,13),(8,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2790_q : Finset ℕ := ([0,1,3,5,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2790_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,11),(0,13),(0,16),(1,3),(1,5),(1,8),(1,11),(1,13),(1,16),(3,5),(3,8),(3,11),(3,13),(3,16),(5,8),(5,11),(5,13),(5,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2791_q : Finset ℕ := ([0,1,3,5,8,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2791_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,11),(0,14),(0,16),(1,3),(1,5),(1,8),(1,11),(1,14),(1,16),(3,5),(3,8),(3,11),(3,14),(3,16),(5,8),(5,11),(5,14),(5,16),(8,11),(8,14),(8,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2792_q : Finset ℕ := ([0,1,3,5,8,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2792_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,12),(0,13),(0,16),(1,3),(1,5),(1,8),(1,12),(1,13),(1,16),(3,5),(3,8),(3,12),(3,13),(3,16),(5,8),(5,12),(5,13),(5,16),(8,12),(8,13),(8,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2793_q : Finset ℕ := ([0,1,3,5,8,12,14,16] : List ℕ).toFinset
noncomputable def certificate_2793_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,8),(0,12),(0,14),(0,16),(1,3),(1,5),(1,8),(1,12),(1,14),(1,16),(3,5),(3,8),(3,12),(3,14),(3,16),(5,8),(5,12),(5,14),(5,16),(8,12),(8,14),(8,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_2794_q : Finset ℕ := ([0,1,3,5,9,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2794_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,9),(0,10),(0,12),(0,15),(1,3),(1,5),(1,9),(1,10),(1,12),(1,15),(3,5),(3,9),(3,10),(3,12),(3,15),(5,9),(5,10),(5,12),(5,15),(9,10),(9,12),(9,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2795_q : Finset ℕ := ([0,1,3,5,9,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2795_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,9),(0,10),(0,12),(0,16),(1,3),(1,5),(1,9),(1,10),(1,12),(1,16),(3,5),(3,9),(3,10),(3,12),(3,16),(5,9),(5,10),(5,12),(5,16),(9,10),(9,12),(9,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2796_q : Finset ℕ := ([0,1,3,5,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2796_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,9),(0,10),(0,13),(0,16),(1,3),(1,5),(1,9),(1,10),(1,13),(1,16),(3,5),(3,9),(3,10),(3,13),(3,16),(5,9),(5,10),(5,13),(5,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2797_q : Finset ℕ := ([0,1,3,5,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2797_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,9),(0,11),(0,12),(0,15),(1,3),(1,5),(1,9),(1,11),(1,12),(1,15),(3,5),(3,9),(3,11),(3,12),(3,15),(5,9),(5,11),(5,12),(5,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2798_q : Finset ℕ := ([0,1,3,5,9,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2798_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,9),(0,11),(0,12),(0,16),(1,3),(1,5),(1,9),(1,11),(1,12),(1,16),(3,5),(3,9),(3,11),(3,12),(3,16),(5,9),(5,11),(5,12),(5,16),(9,11),(9,12),(9,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2799_q : Finset ℕ := ([0,1,3,5,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2799_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,9),(0,11),(0,13),(0,16),(1,3),(1,5),(1,9),(1,11),(1,13),(1,16),(3,5),(3,9),(3,11),(3,13),(3,16),(5,9),(5,11),(5,13),(5,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2800_q : Finset ℕ := ([0,1,3,5,9,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2800_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,9),(0,11),(0,14),(0,16),(1,3),(1,5),(1,9),(1,11),(1,14),(1,16),(3,5),(3,9),(3,11),(3,14),(3,16),(5,9),(5,11),(5,14),(5,16),(9,11),(9,14),(9,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2801_q : Finset ℕ := ([0,1,3,5,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2801_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,9),(0,12),(0,13),(0,16),(1,3),(1,5),(1,9),(1,12),(1,13),(1,16),(3,5),(3,9),(3,12),(3,13),(3,16),(5,9),(5,12),(5,13),(5,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2802_q : Finset ℕ := ([0,1,3,5,10,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2802_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,10),(0,11),(0,13),(0,16),(1,3),(1,5),(1,10),(1,11),(1,13),(1,16),(3,5),(3,10),(3,11),(3,13),(3,16),(5,10),(5,11),(5,13),(5,16),(10,11),(10,13),(10,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2803_q : Finset ℕ := ([0,1,3,5,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2803_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,5),(0,10),(0,12),(0,13),(0,16),(1,3),(1,5),(1,10),(1,12),(1,13),(1,16),(3,5),(3,10),(3,12),(3,13),(3,16),(5,10),(5,12),(5,13),(5,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2804_q : Finset ℕ := ([0,1,3,6,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2804_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(0,14),(1,3),(1,6),(1,7),(1,9),(1,12),(1,14),(3,6),(3,7),(3,9),(3,12),(3,14),(6,7),(6,9),(6,12),(6,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2805_q : Finset ℕ := ([0,1,3,6,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2805_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(0,15),(1,3),(1,6),(1,7),(1,9),(1,12),(1,15),(3,6),(3,7),(3,9),(3,12),(3,15),(6,7),(6,9),(6,12),(6,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2806_q : Finset ℕ := ([0,1,3,6,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2806_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(0,16),(1,3),(1,6),(1,7),(1,9),(1,12),(1,16),(3,6),(3,7),(3,9),(3,12),(3,16),(6,7),(6,9),(6,12),(6,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2807_q : Finset ℕ := ([0,1,3,6,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2807_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,9),(0,13),(0,15),(1,3),(1,6),(1,7),(1,9),(1,13),(1,15),(3,6),(3,7),(3,9),(3,13),(3,15),(6,7),(6,9),(6,13),(6,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2808_q : Finset ℕ := ([0,1,3,6,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2808_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,9),(0,13),(0,16),(1,3),(1,6),(1,7),(1,9),(1,13),(1,16),(3,6),(3,7),(3,9),(3,13),(3,16),(6,7),(6,9),(6,13),(6,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2809_q : Finset ℕ := ([0,1,3,6,7,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2809_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,9),(0,14),(0,16),(1,3),(1,6),(1,7),(1,9),(1,14),(1,16),(3,6),(3,7),(3,9),(3,14),(3,16),(6,7),(6,9),(6,14),(6,16),(7,9),(7,14),(7,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2810_q : Finset ℕ := ([0,1,3,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2810_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,10),(0,11),(0,14),(1,3),(1,6),(1,7),(1,10),(1,11),(1,14),(3,6),(3,7),(3,10),(3,11),(3,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2811_q : Finset ℕ := ([0,1,3,6,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2811_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,10),(0,11),(0,15),(1,3),(1,6),(1,7),(1,10),(1,11),(1,15),(3,6),(3,7),(3,10),(3,11),(3,15),(6,7),(6,10),(6,11),(6,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2812_q : Finset ℕ := ([0,1,3,6,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2812_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,10),(0,11),(0,16),(1,3),(1,6),(1,7),(1,10),(1,11),(1,16),(3,6),(3,7),(3,10),(3,11),(3,16),(6,7),(6,10),(6,11),(6,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2813_q : Finset ℕ := ([0,1,3,6,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2813_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,10),(0,12),(0,15),(1,3),(1,6),(1,7),(1,10),(1,12),(1,15),(3,6),(3,7),(3,10),(3,12),(3,15),(6,7),(6,10),(6,12),(6,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2814_q : Finset ℕ := ([0,1,3,6,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2814_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,10),(0,12),(0,16),(1,3),(1,6),(1,7),(1,10),(1,12),(1,16),(3,6),(3,7),(3,10),(3,12),(3,16),(6,7),(6,10),(6,12),(6,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2815_q : Finset ℕ := ([0,1,3,6,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2815_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,10),(0,13),(0,16),(1,3),(1,6),(1,7),(1,10),(1,13),(1,16),(3,6),(3,7),(3,10),(3,13),(3,16),(6,7),(6,10),(6,13),(6,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

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

noncomputable def certificate_2816_q : Finset ℕ := ([0,1,3,6,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2816_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,7),(0,11),(0,12),(0,16),(1,3),(1,6),(1,7),(1,11),(1,12),(1,16),(3,6),(3,7),(3,11),(3,12),(3,16),(6,7),(6,11),(6,12),(6,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2817_q : Finset ℕ := ([0,1,3,6,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2817_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,9),(0,11),(0,15),(1,3),(1,6),(1,8),(1,9),(1,11),(1,15),(3,6),(3,8),(3,9),(3,11),(3,15),(6,8),(6,9),(6,11),(6,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2818_q : Finset ℕ := ([0,1,3,6,8,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2818_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,9),(0,11),(0,16),(1,3),(1,6),(1,8),(1,9),(1,11),(1,16),(3,6),(3,8),(3,9),(3,11),(3,16),(6,8),(6,9),(6,11),(6,16),(8,9),(8,11),(8,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2819_q : Finset ℕ := ([0,1,3,6,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2819_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,9),(0,12),(0,15),(1,3),(1,6),(1,8),(1,9),(1,12),(1,15),(3,6),(3,8),(3,9),(3,12),(3,15),(6,8),(6,9),(6,12),(6,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2820_q : Finset ℕ := ([0,1,3,6,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2820_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,9),(0,12),(0,16),(1,3),(1,6),(1,8),(1,9),(1,12),(1,16),(3,6),(3,8),(3,9),(3,12),(3,16),(6,8),(6,9),(6,12),(6,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2821_q : Finset ℕ := ([0,1,3,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2821_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,10),(0,12),(0,15),(1,3),(1,6),(1,8),(1,10),(1,12),(1,15),(3,6),(3,8),(3,10),(3,12),(3,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2822_q : Finset ℕ := ([0,1,3,6,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2822_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,10),(0,12),(0,16),(1,3),(1,6),(1,8),(1,10),(1,12),(1,16),(3,6),(3,8),(3,10),(3,12),(3,16),(6,8),(6,10),(6,12),(6,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2823_q : Finset ℕ := ([0,1,3,6,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2823_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,10),(0,13),(0,15),(1,3),(1,6),(1,8),(1,10),(1,13),(1,15),(3,6),(3,8),(3,10),(3,13),(3,15),(6,8),(6,10),(6,13),(6,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2824_q : Finset ℕ := ([0,1,3,6,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2824_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,10),(0,13),(0,16),(1,3),(1,6),(1,8),(1,10),(1,13),(1,16),(3,6),(3,8),(3,10),(3,13),(3,16),(6,8),(6,10),(6,13),(6,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2825_q : Finset ℕ := ([0,1,3,6,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2825_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,10),(0,14),(0,16),(1,3),(1,6),(1,8),(1,10),(1,14),(1,16),(3,6),(3,8),(3,10),(3,14),(3,16),(6,8),(6,10),(6,14),(6,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2826_q : Finset ℕ := ([0,1,3,6,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2826_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,11),(0,12),(0,15),(1,3),(1,6),(1,8),(1,11),(1,12),(1,15),(3,6),(3,8),(3,11),(3,12),(3,15),(6,8),(6,11),(6,12),(6,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2827_q : Finset ℕ := ([0,1,3,6,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2827_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,11),(0,12),(0,16),(1,3),(1,6),(1,8),(1,11),(1,12),(1,16),(3,6),(3,8),(3,11),(3,12),(3,16),(6,8),(6,11),(6,12),(6,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2828_q : Finset ℕ := ([0,1,3,6,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2828_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,11),(0,13),(0,16),(1,3),(1,6),(1,8),(1,11),(1,13),(1,16),(3,6),(3,8),(3,11),(3,13),(3,16),(6,8),(6,11),(6,13),(6,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2829_q : Finset ℕ := ([0,1,3,6,8,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2829_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,11),(0,14),(0,16),(1,3),(1,6),(1,8),(1,11),(1,14),(1,16),(3,6),(3,8),(3,11),(3,14),(3,16),(6,8),(6,11),(6,14),(6,16),(8,11),(8,14),(8,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2830_q : Finset ℕ := ([0,1,3,6,8,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2830_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,8),(0,12),(0,13),(0,16),(1,3),(1,6),(1,8),(1,12),(1,13),(1,16),(3,6),(3,8),(3,12),(3,13),(3,16),(6,8),(6,12),(6,13),(6,16),(8,12),(8,13),(8,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2831_q : Finset ℕ := ([0,1,3,6,9,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2831_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,9),(0,10),(0,12),(0,16),(1,3),(1,6),(1,9),(1,10),(1,12),(1,16),(3,6),(3,9),(3,10),(3,12),(3,16),(6,9),(6,10),(6,12),(6,16),(9,10),(9,12),(9,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2832_q : Finset ℕ := ([0,1,3,6,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2832_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,9),(0,10),(0,13),(0,16),(1,3),(1,6),(1,9),(1,10),(1,13),(1,16),(3,6),(3,9),(3,10),(3,13),(3,16),(6,9),(6,10),(6,13),(6,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2833_q : Finset ℕ := ([0,1,3,6,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2833_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,9),(0,11),(0,12),(0,15),(1,3),(1,6),(1,9),(1,11),(1,12),(1,15),(3,6),(3,9),(3,11),(3,12),(3,15),(6,9),(6,11),(6,12),(6,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2834_q : Finset ℕ := ([0,1,3,6,9,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2834_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,9),(0,11),(0,12),(0,16),(1,3),(1,6),(1,9),(1,11),(1,12),(1,16),(3,6),(3,9),(3,11),(3,12),(3,16),(6,9),(6,11),(6,12),(6,16),(9,11),(9,12),(9,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2835_q : Finset ℕ := ([0,1,3,6,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2835_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,9),(0,11),(0,13),(0,16),(1,3),(1,6),(1,9),(1,11),(1,13),(1,16),(3,6),(3,9),(3,11),(3,13),(3,16),(6,9),(6,11),(6,13),(6,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2836_q : Finset ℕ := ([0,1,3,6,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2836_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,9),(0,12),(0,13),(0,16),(1,3),(1,6),(1,9),(1,12),(1,13),(1,16),(3,6),(3,9),(3,12),(3,13),(3,16),(6,9),(6,12),(6,13),(6,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2837_q : Finset ℕ := ([0,1,3,6,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2837_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,6),(0,10),(0,12),(0,13),(0,16),(1,3),(1,6),(1,10),(1,12),(1,13),(1,16),(3,6),(3,10),(3,12),(3,13),(3,16),(6,10),(6,12),(6,13),(6,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2838_q : Finset ℕ := ([0,1,3,7,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2838_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,7),(0,8),(0,10),(0,14),(0,16),(1,3),(1,7),(1,8),(1,10),(1,14),(1,16),(3,7),(3,8),(3,10),(3,14),(3,16),(7,8),(7,10),(7,14),(7,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2839_q : Finset ℕ := ([0,1,3,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2839_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,7),(0,8),(0,11),(0,12),(0,15),(1,3),(1,7),(1,8),(1,11),(1,12),(1,15),(3,7),(3,8),(3,11),(3,12),(3,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2840_q : Finset ℕ := ([0,1,3,7,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2840_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,7),(0,8),(0,11),(0,12),(0,16),(1,3),(1,7),(1,8),(1,11),(1,12),(1,16),(3,7),(3,8),(3,11),(3,12),(3,16),(7,8),(7,11),(7,12),(7,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2841_q : Finset ℕ := ([0,1,3,7,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2841_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,7),(0,8),(0,11),(0,13),(0,16),(1,3),(1,7),(1,8),(1,11),(1,13),(1,16),(3,7),(3,8),(3,11),(3,13),(3,16),(7,8),(7,11),(7,13),(7,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2842_q : Finset ℕ := ([0,1,3,7,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2842_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,7),(0,9),(0,10),(0,13),(0,16),(1,3),(1,7),(1,9),(1,10),(1,13),(1,16),(3,7),(3,9),(3,10),(3,13),(3,16),(7,9),(7,10),(7,13),(7,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2843_q : Finset ℕ := ([0,1,3,7,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2843_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,3),(0,7),(0,9),(0,11),(0,13),(0,16),(1,3),(1,7),(1,9),(1,11),(1,13),(1,16),(3,7),(3,9),(3,11),(3,13),(3,16),(7,9),(7,11),(7,13),(7,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2844_q : Finset ℕ := ([0,1,3,7,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2844_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,7),(0,9),(0,12),(0,13),(0,16),(1,3),(1,7),(1,9),(1,12),(1,13),(1,16),(3,7),(3,9),(3,12),(3,13),(3,16),(7,9),(7,12),(7,13),(7,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2845_q : Finset ℕ := ([0,1,3,8,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2845_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,3),(0,8),(0,9),(0,12),(0,13),(0,16),(1,3),(1,8),(1,9),(1,12),(1,13),(1,16),(3,8),(3,9),(3,12),(3,13),(3,16),(8,9),(8,12),(8,13),(8,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2846_q : Finset ℕ := ([0,1,4,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2846_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,4),(0,5),(0,8),(0,9),(0,12),(0,15),(1,4),(1,5),(1,8),(1,9),(1,12),(1,15),(4,5),(4,8),(4,9),(4,12),(4,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2847_q : Finset ℕ := ([0,1,4,5,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2847_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,5),(0,8),(0,9),(0,12),(0,16),(1,4),(1,5),(1,8),(1,9),(1,12),(1,16),(4,5),(4,8),(4,9),(4,12),(4,16),(5,8),(5,9),(5,12),(5,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

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

noncomputable def certificate_2848_q : Finset ℕ := ([0,1,4,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2848_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,4),(0,5),(0,8),(0,10),(0,12),(0,15),(1,4),(1,5),(1,8),(1,10),(1,12),(1,15),(4,5),(4,8),(4,10),(4,12),(4,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2849_q : Finset ℕ := ([0,1,4,5,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2849_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,5),(0,8),(0,10),(0,12),(0,16),(1,4),(1,5),(1,8),(1,10),(1,12),(1,16),(4,5),(4,8),(4,10),(4,12),(4,16),(5,8),(5,10),(5,12),(5,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2850_q : Finset ℕ := ([0,1,4,5,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2850_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,5),(0,8),(0,10),(0,13),(0,16),(1,4),(1,5),(1,8),(1,10),(1,13),(1,16),(4,5),(4,8),(4,10),(4,13),(4,16),(5,8),(5,10),(5,13),(5,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2851_q : Finset ℕ := ([0,1,4,5,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2851_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,5),(0,8),(0,11),(0,12),(0,16),(1,4),(1,5),(1,8),(1,11),(1,12),(1,16),(4,5),(4,8),(4,11),(4,12),(4,16),(5,8),(5,11),(5,12),(5,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2852_q : Finset ℕ := ([0,1,4,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2852_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,4),(0,6),(0,8),(0,10),(0,12),(0,15),(1,4),(1,6),(1,8),(1,10),(1,12),(1,15),(4,6),(4,8),(4,10),(4,12),(4,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2853_q : Finset ℕ := ([0,1,4,6,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2853_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,6),(0,8),(0,10),(0,12),(0,16),(1,4),(1,6),(1,8),(1,10),(1,12),(1,16),(4,6),(4,8),(4,10),(4,12),(4,16),(6,8),(6,10),(6,12),(6,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2854_q : Finset ℕ := ([0,1,4,6,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2854_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,6),(0,8),(0,10),(0,13),(0,16),(1,4),(1,6),(1,8),(1,10),(1,13),(1,16),(4,6),(4,8),(4,10),(4,13),(4,16),(6,8),(6,10),(6,13),(6,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2855_q : Finset ℕ := ([0,1,4,6,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2855_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,6),(0,8),(0,11),(0,12),(0,16),(1,4),(1,6),(1,8),(1,11),(1,12),(1,16),(4,6),(4,8),(4,11),(4,12),(4,16),(6,8),(6,11),(6,12),(6,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2856_q : Finset ℕ := ([0,1,4,6,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2856_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,6),(0,8),(0,11),(0,13),(0,16),(1,4),(1,6),(1,8),(1,11),(1,13),(1,16),(4,6),(4,8),(4,11),(4,13),(4,16),(6,8),(6,11),(6,13),(6,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2857_q : Finset ℕ := ([0,1,4,6,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2857_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,4),(0,6),(0,9),(0,10),(0,13),(0,16),(1,4),(1,6),(1,9),(1,10),(1,13),(1,16),(4,6),(4,9),(4,10),(4,13),(4,16),(6,9),(6,10),(6,13),(6,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2858_q : Finset ℕ := ([0,2,3,5,6,8,9,11] : List ℕ).toFinset
noncomputable def certificate_2858_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,11),(2,3),(2,5),(2,6),(2,8),(2,9),(2,11),(3,5),(3,6),(3,8),(3,9),(3,11),(5,6),(5,8),(5,9),(5,11),(6,8),(6,9),(6,11),(8,9),(8,11),(9,11)]

noncomputable def certificate_2859_q : Finset ℕ := ([0,2,3,5,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2859_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,12),(2,3),(2,5),(2,6),(2,8),(2,9),(2,12),(3,5),(3,6),(3,8),(3,9),(3,12),(5,6),(5,8),(5,9),(5,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2860_q : Finset ℕ := ([0,2,3,5,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2860_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,13),(2,3),(2,5),(2,6),(2,8),(2,9),(2,13),(3,5),(3,6),(3,8),(3,9),(3,13),(5,6),(5,8),(5,9),(5,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2861_q : Finset ℕ := ([0,2,3,5,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2861_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,14),(2,3),(2,5),(2,6),(2,8),(2,9),(2,14),(3,5),(3,6),(3,8),(3,9),(3,14),(5,6),(5,8),(5,9),(5,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2862_q : Finset ℕ := ([0,2,3,5,6,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2862_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,15),(2,3),(2,5),(2,6),(2,8),(2,9),(2,15),(3,5),(3,6),(3,8),(3,9),(3,15),(5,6),(5,8),(5,9),(5,15),(6,8),(6,9),(6,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2863_q : Finset ℕ := ([0,2,3,5,6,8,9,16] : List ℕ).toFinset
noncomputable def certificate_2863_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,16),(2,3),(2,5),(2,6),(2,8),(2,9),(2,16),(3,5),(3,6),(3,8),(3,9),(3,16),(5,6),(5,8),(5,9),(5,16),(6,8),(6,9),(6,16),(8,9),(8,16),(9,16)]

noncomputable def certificate_2864_q : Finset ℕ := ([0,2,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2864_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(2,3),(2,5),(2,6),(2,8),(2,10),(2,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2865_q : Finset ℕ := ([0,2,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2865_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(2,3),(2,5),(2,6),(2,8),(2,10),(2,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2866_q : Finset ℕ := ([0,2,3,5,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2866_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,14),(2,3),(2,5),(2,6),(2,8),(2,10),(2,14),(3,5),(3,6),(3,8),(3,10),(3,14),(5,6),(5,8),(5,10),(5,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2867_q : Finset ℕ := ([0,2,3,5,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2867_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,15),(2,3),(2,5),(2,6),(2,8),(2,10),(2,15),(3,5),(3,6),(3,8),(3,10),(3,15),(5,6),(5,8),(5,10),(5,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2868_q : Finset ℕ := ([0,2,3,5,6,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2868_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,16),(2,3),(2,5),(2,6),(2,8),(2,10),(2,16),(3,5),(3,6),(3,8),(3,10),(3,16),(5,6),(5,8),(5,10),(5,16),(6,8),(6,10),(6,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2869_q : Finset ℕ := ([0,2,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2869_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(2,3),(2,5),(2,6),(2,8),(2,11),(2,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2870_q : Finset ℕ := ([0,2,3,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2870_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,14),(2,3),(2,5),(2,6),(2,8),(2,11),(2,14),(3,5),(3,6),(3,8),(3,11),(3,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2871_q : Finset ℕ := ([0,2,3,5,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2871_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,15),(2,3),(2,5),(2,6),(2,8),(2,11),(2,15),(3,5),(3,6),(3,8),(3,11),(3,15),(5,6),(5,8),(5,11),(5,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2872_q : Finset ℕ := ([0,2,3,5,6,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2872_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,16),(2,3),(2,5),(2,6),(2,8),(2,11),(2,16),(3,5),(3,6),(3,8),(3,11),(3,16),(5,6),(5,8),(5,11),(5,16),(6,8),(6,11),(6,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2873_q : Finset ℕ := ([0,2,3,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2873_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(0,14),(2,3),(2,5),(2,6),(2,8),(2,12),(2,14),(3,5),(3,6),(3,8),(3,12),(3,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2874_q : Finset ℕ := ([0,2,3,5,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2874_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(0,15),(2,3),(2,5),(2,6),(2,8),(2,12),(2,15),(3,5),(3,6),(3,8),(3,12),(3,15),(5,6),(5,8),(5,12),(5,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2875_q : Finset ℕ := ([0,2,3,5,6,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2875_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(0,16),(2,3),(2,5),(2,6),(2,8),(2,12),(2,16),(3,5),(3,6),(3,8),(3,12),(3,16),(5,6),(5,8),(5,12),(5,16),(6,8),(6,12),(6,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2876_q : Finset ℕ := ([0,2,3,5,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2876_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(0,15),(2,3),(2,5),(2,6),(2,8),(2,13),(2,15),(3,5),(3,6),(3,8),(3,13),(3,15),(5,6),(5,8),(5,13),(5,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2877_q : Finset ℕ := ([0,2,3,5,6,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2877_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(0,16),(2,3),(2,5),(2,6),(2,8),(2,13),(2,16),(3,5),(3,6),(3,8),(3,13),(3,16),(5,6),(5,8),(5,13),(5,16),(6,8),(6,13),(6,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2878_q : Finset ℕ := ([0,2,3,5,6,8,14,16] : List ℕ).toFinset
noncomputable def certificate_2878_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,8),(0,14),(0,16),(2,3),(2,5),(2,6),(2,8),(2,14),(2,16),(3,5),(3,6),(3,8),(3,14),(3,16),(5,6),(5,8),(5,14),(5,16),(6,8),(6,14),(6,16),(8,14),(8,16),(14,16)]

noncomputable def certificate_2879_q : Finset ℕ := ([0,2,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2879_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(2,3),(2,5),(2,6),(2,9),(2,10),(2,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

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

noncomputable def certificate_2880_q : Finset ℕ := ([0,2,3,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2880_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,14),(2,3),(2,5),(2,6),(2,9),(2,10),(2,14),(3,5),(3,6),(3,9),(3,10),(3,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2881_q : Finset ℕ := ([0,2,3,5,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2881_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,15),(2,3),(2,5),(2,6),(2,9),(2,10),(2,15),(3,5),(3,6),(3,9),(3,10),(3,15),(5,6),(5,9),(5,10),(5,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2882_q : Finset ℕ := ([0,2,3,5,6,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2882_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,16),(2,3),(2,5),(2,6),(2,9),(2,10),(2,16),(3,5),(3,6),(3,9),(3,10),(3,16),(5,6),(5,9),(5,10),(5,16),(6,9),(6,10),(6,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2883_q : Finset ℕ := ([0,2,3,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2883_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,11),(0,14),(2,3),(2,5),(2,6),(2,9),(2,11),(2,14),(3,5),(3,6),(3,9),(3,11),(3,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2884_q : Finset ℕ := ([0,2,3,5,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2884_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,9),(0,11),(0,15),(2,3),(2,5),(2,6),(2,9),(2,11),(2,15),(3,5),(3,6),(3,9),(3,11),(3,15),(5,6),(5,9),(5,11),(5,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2885_q : Finset ℕ := ([0,2,3,5,6,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2885_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,9),(0,11),(0,16),(2,3),(2,5),(2,6),(2,9),(2,11),(2,16),(3,5),(3,6),(3,9),(3,11),(3,16),(5,6),(5,9),(5,11),(5,16),(6,9),(6,11),(6,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2886_q : Finset ℕ := ([0,2,3,5,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2886_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(0,15),(2,3),(2,5),(2,6),(2,9),(2,12),(2,15),(3,5),(3,6),(3,9),(3,12),(3,15),(5,6),(5,9),(5,12),(5,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2887_q : Finset ℕ := ([0,2,3,5,6,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2887_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(0,16),(2,3),(2,5),(2,6),(2,9),(2,12),(2,16),(3,5),(3,6),(3,9),(3,12),(3,16),(5,6),(5,9),(5,12),(5,16),(6,9),(6,12),(6,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2888_q : Finset ℕ := ([0,2,3,5,6,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2888_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(0,16),(2,3),(2,5),(2,6),(2,9),(2,13),(2,16),(3,5),(3,6),(3,9),(3,13),(3,16),(5,6),(5,9),(5,13),(5,16),(6,9),(6,13),(6,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2889_q : Finset ℕ := ([0,2,3,5,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2889_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,10),(0,11),(0,15),(2,3),(2,5),(2,6),(2,10),(2,11),(2,15),(3,5),(3,6),(3,10),(3,11),(3,15),(5,6),(5,10),(5,11),(5,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2890_q : Finset ℕ := ([0,2,3,5,6,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2890_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,10),(0,11),(0,16),(2,3),(2,5),(2,6),(2,10),(2,11),(2,16),(3,5),(3,6),(3,10),(3,11),(3,16),(5,6),(5,10),(5,11),(5,16),(6,10),(6,11),(6,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2891_q : Finset ℕ := ([0,2,3,5,6,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2891_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,6),(0,10),(0,12),(0,16),(2,3),(2,5),(2,6),(2,10),(2,12),(2,16),(3,5),(3,6),(3,10),(3,12),(3,16),(5,6),(5,10),(5,12),(5,16),(6,10),(6,12),(6,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2892_q : Finset ℕ := ([0,2,3,5,7,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2892_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,12),(2,3),(2,5),(2,7),(2,8),(2,10),(2,12),(3,5),(3,7),(3,8),(3,10),(3,12),(5,7),(5,8),(5,10),(5,12),(7,8),(7,10),(7,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2893_q : Finset ℕ := ([0,2,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2893_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(2,3),(2,5),(2,7),(2,8),(2,10),(2,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2894_q : Finset ℕ := ([0,2,3,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2894_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,14),(2,3),(2,5),(2,7),(2,8),(2,10),(2,14),(3,5),(3,7),(3,8),(3,10),(3,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2895_q : Finset ℕ := ([0,2,3,5,7,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2895_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,15),(2,3),(2,5),(2,7),(2,8),(2,10),(2,15),(3,5),(3,7),(3,8),(3,10),(3,15),(5,7),(5,8),(5,10),(5,15),(7,8),(7,10),(7,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2896_q : Finset ℕ := ([0,2,3,5,7,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2896_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,16),(2,3),(2,5),(2,7),(2,8),(2,10),(2,16),(3,5),(3,7),(3,8),(3,10),(3,16),(5,7),(5,8),(5,10),(5,16),(7,8),(7,10),(7,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2897_q : Finset ℕ := ([0,2,3,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2897_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(0,14),(2,3),(2,5),(2,7),(2,8),(2,11),(2,14),(3,5),(3,7),(3,8),(3,11),(3,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2898_q : Finset ℕ := ([0,2,3,5,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2898_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(0,15),(2,3),(2,5),(2,7),(2,8),(2,11),(2,15),(3,5),(3,7),(3,8),(3,11),(3,15),(5,7),(5,8),(5,11),(5,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2899_q : Finset ℕ := ([0,2,3,5,7,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2899_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(0,16),(2,3),(2,5),(2,7),(2,8),(2,11),(2,16),(3,5),(3,7),(3,8),(3,11),(3,16),(5,7),(5,8),(5,11),(5,16),(7,8),(7,11),(7,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2900_q : Finset ℕ := ([0,2,3,5,7,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2900_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(0,16),(2,3),(2,5),(2,7),(2,8),(2,12),(2,16),(3,5),(3,7),(3,8),(3,12),(3,16),(5,7),(5,8),(5,12),(5,16),(7,8),(7,12),(7,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2901_q : Finset ℕ := ([0,2,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2901_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(2,3),(2,5),(2,7),(2,9),(2,10),(2,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2902_q : Finset ℕ := ([0,2,3,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2902_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,14),(2,3),(2,5),(2,7),(2,9),(2,10),(2,14),(3,5),(3,7),(3,9),(3,10),(3,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2903_q : Finset ℕ := ([0,2,3,5,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2903_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,15),(2,3),(2,5),(2,7),(2,9),(2,10),(2,15),(3,5),(3,7),(3,9),(3,10),(3,15),(5,7),(5,9),(5,10),(5,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2904_q : Finset ℕ := ([0,2,3,5,7,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2904_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,16),(2,3),(2,5),(2,7),(2,9),(2,10),(2,16),(3,5),(3,7),(3,9),(3,10),(3,16),(5,7),(5,9),(5,10),(5,16),(7,9),(7,10),(7,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2905_q : Finset ℕ := ([0,2,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2905_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(2,3),(2,5),(2,7),(2,9),(2,11),(2,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2906_q : Finset ℕ := ([0,2,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2906_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(2,3),(2,5),(2,7),(2,9),(2,11),(2,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2907_q : Finset ℕ := ([0,2,3,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2907_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,15),(2,3),(2,5),(2,7),(2,9),(2,11),(2,15),(3,5),(3,7),(3,9),(3,11),(3,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2908_q : Finset ℕ := ([0,2,3,5,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2908_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,16),(2,3),(2,5),(2,7),(2,9),(2,11),(2,16),(3,5),(3,7),(3,9),(3,11),(3,16),(5,7),(5,9),(5,11),(5,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2909_q : Finset ℕ := ([0,2,3,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2909_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(0,14),(2,3),(2,5),(2,7),(2,9),(2,12),(2,14),(3,5),(3,7),(3,9),(3,12),(3,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2910_q : Finset ℕ := ([0,2,3,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2910_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(0,15),(2,3),(2,5),(2,7),(2,9),(2,12),(2,15),(3,5),(3,7),(3,9),(3,12),(3,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2911_q : Finset ℕ := ([0,2,3,5,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2911_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(0,16),(2,3),(2,5),(2,7),(2,9),(2,12),(2,16),(3,5),(3,7),(3,9),(3,12),(3,16),(5,7),(5,9),(5,12),(5,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

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

noncomputable def certificate_2912_q : Finset ℕ := ([0,2,3,5,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2912_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(0,15),(2,3),(2,5),(2,7),(2,9),(2,13),(2,15),(3,5),(3,7),(3,9),(3,13),(3,15),(5,7),(5,9),(5,13),(5,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2913_q : Finset ℕ := ([0,2,3,5,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2913_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(0,16),(2,3),(2,5),(2,7),(2,9),(2,13),(2,16),(3,5),(3,7),(3,9),(3,13),(3,16),(5,7),(5,9),(5,13),(5,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2914_q : Finset ℕ := ([0,2,3,5,7,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2914_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,9),(0,14),(0,16),(2,3),(2,5),(2,7),(2,9),(2,14),(2,16),(3,5),(3,7),(3,9),(3,14),(3,16),(5,7),(5,9),(5,14),(5,16),(7,9),(7,14),(7,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2915_q : Finset ℕ := ([0,2,3,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2915_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,11),(0,14),(2,3),(2,5),(2,7),(2,10),(2,11),(2,14),(3,5),(3,7),(3,10),(3,11),(3,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2916_q : Finset ℕ := ([0,2,3,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2916_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,10),(0,11),(0,15),(2,3),(2,5),(2,7),(2,10),(2,11),(2,15),(3,5),(3,7),(3,10),(3,11),(3,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2917_q : Finset ℕ := ([0,2,3,5,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2917_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,10),(0,11),(0,16),(2,3),(2,5),(2,7),(2,10),(2,11),(2,16),(3,5),(3,7),(3,10),(3,11),(3,16),(5,7),(5,10),(5,11),(5,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2918_q : Finset ℕ := ([0,2,3,5,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_2918_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(0,14),(2,3),(2,5),(2,7),(2,10),(2,12),(2,14),(3,5),(3,7),(3,10),(3,12),(3,14),(5,7),(5,10),(5,12),(5,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_2919_q : Finset ℕ := ([0,2,3,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2919_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(0,15),(2,3),(2,5),(2,7),(2,10),(2,12),(2,15),(3,5),(3,7),(3,10),(3,12),(3,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2920_q : Finset ℕ := ([0,2,3,5,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2920_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(0,16),(2,3),(2,5),(2,7),(2,10),(2,12),(2,16),(3,5),(3,7),(3,10),(3,12),(3,16),(5,7),(5,10),(5,12),(5,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2921_q : Finset ℕ := ([0,2,3,5,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2921_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(0,15),(2,3),(2,5),(2,7),(2,10),(2,13),(2,15),(3,5),(3,7),(3,10),(3,13),(3,15),(5,7),(5,10),(5,13),(5,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2922_q : Finset ℕ := ([0,2,3,5,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2922_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(0,16),(2,3),(2,5),(2,7),(2,10),(2,13),(2,16),(3,5),(3,7),(3,10),(3,13),(3,16),(5,7),(5,10),(5,13),(5,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2923_q : Finset ℕ := ([0,2,3,5,7,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2923_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,10),(0,14),(0,16),(2,3),(2,5),(2,7),(2,10),(2,14),(2,16),(3,5),(3,7),(3,10),(3,14),(3,16),(5,7),(5,10),(5,14),(5,16),(7,10),(7,14),(7,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2924_q : Finset ℕ := ([0,2,3,5,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2924_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,11),(0,12),(0,15),(2,3),(2,5),(2,7),(2,11),(2,12),(2,15),(3,5),(3,7),(3,11),(3,12),(3,15),(5,7),(5,11),(5,12),(5,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2925_q : Finset ℕ := ([0,2,3,5,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2925_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,11),(0,12),(0,16),(2,3),(2,5),(2,7),(2,11),(2,12),(2,16),(3,5),(3,7),(3,11),(3,12),(3,16),(5,7),(5,11),(5,12),(5,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2926_q : Finset ℕ := ([0,2,3,5,7,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2926_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(0,15),(2,3),(2,5),(2,7),(2,11),(2,13),(2,15),(3,5),(3,7),(3,11),(3,13),(3,15),(5,7),(5,11),(5,13),(5,15),(7,11),(7,13),(7,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2927_q : Finset ℕ := ([0,2,3,5,7,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2927_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(0,16),(2,3),(2,5),(2,7),(2,11),(2,13),(2,16),(3,5),(3,7),(3,11),(3,13),(3,16),(5,7),(5,11),(5,13),(5,16),(7,11),(7,13),(7,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2928_q : Finset ℕ := ([0,2,3,5,7,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2928_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,11),(0,14),(0,16),(2,3),(2,5),(2,7),(2,11),(2,14),(2,16),(3,5),(3,7),(3,11),(3,14),(3,16),(5,7),(5,11),(5,14),(5,16),(7,11),(7,14),(7,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2929_q : Finset ℕ := ([0,2,3,5,7,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2929_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,12),(0,13),(0,16),(2,3),(2,5),(2,7),(2,12),(2,13),(2,16),(3,5),(3,7),(3,12),(3,13),(3,16),(5,7),(5,12),(5,13),(5,16),(7,12),(7,13),(7,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2930_q : Finset ℕ := ([0,2,3,5,7,12,14,16] : List ℕ).toFinset
noncomputable def certificate_2930_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,7),(0,12),(0,14),(0,16),(2,3),(2,5),(2,7),(2,12),(2,14),(2,16),(3,5),(3,7),(3,12),(3,14),(3,16),(5,7),(5,12),(5,14),(5,16),(7,12),(7,14),(7,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_2931_q : Finset ℕ := ([0,2,3,5,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2931_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,9),(0,11),(0,14),(2,3),(2,5),(2,8),(2,9),(2,11),(2,14),(3,5),(3,8),(3,9),(3,11),(3,14),(5,8),(5,9),(5,11),(5,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2932_q : Finset ℕ := ([0,2,3,5,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2932_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,9),(0,11),(0,15),(2,3),(2,5),(2,8),(2,9),(2,11),(2,15),(3,5),(3,8),(3,9),(3,11),(3,15),(5,8),(5,9),(5,11),(5,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2933_q : Finset ℕ := ([0,2,3,5,8,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2933_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,9),(0,11),(0,16),(2,3),(2,5),(2,8),(2,9),(2,11),(2,16),(3,5),(3,8),(3,9),(3,11),(3,16),(5,8),(5,9),(5,11),(5,16),(8,9),(8,11),(8,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2934_q : Finset ℕ := ([0,2,3,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2934_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(0,15),(2,3),(2,5),(2,8),(2,9),(2,12),(2,15),(3,5),(3,8),(3,9),(3,12),(3,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2935_q : Finset ℕ := ([0,2,3,5,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2935_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(0,16),(2,3),(2,5),(2,8),(2,9),(2,12),(2,16),(3,5),(3,8),(3,9),(3,12),(3,16),(5,8),(5,9),(5,12),(5,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2936_q : Finset ℕ := ([0,2,3,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2936_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,10),(0,11),(0,14),(2,3),(2,5),(2,8),(2,10),(2,11),(2,14),(3,5),(3,8),(3,10),(3,11),(3,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2937_q : Finset ℕ := ([0,2,3,5,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2937_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,10),(0,11),(0,15),(2,3),(2,5),(2,8),(2,10),(2,11),(2,15),(3,5),(3,8),(3,10),(3,11),(3,15),(5,8),(5,10),(5,11),(5,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2938_q : Finset ℕ := ([0,2,3,5,8,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2938_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,10),(0,11),(0,16),(2,3),(2,5),(2,8),(2,10),(2,11),(2,16),(3,5),(3,8),(3,10),(3,11),(3,16),(5,8),(5,10),(5,11),(5,16),(8,10),(8,11),(8,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2939_q : Finset ℕ := ([0,2,3,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2939_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,10),(0,12),(0,15),(2,3),(2,5),(2,8),(2,10),(2,12),(2,15),(3,5),(3,8),(3,10),(3,12),(3,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2940_q : Finset ℕ := ([0,2,3,5,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2940_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,10),(0,12),(0,16),(2,3),(2,5),(2,8),(2,10),(2,12),(2,16),(3,5),(3,8),(3,10),(3,12),(3,16),(5,8),(5,10),(5,12),(5,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2941_q : Finset ℕ := ([0,2,3,5,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2941_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(0,15),(2,3),(2,5),(2,8),(2,10),(2,13),(2,15),(3,5),(3,8),(3,10),(3,13),(3,15),(5,8),(5,10),(5,13),(5,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2942_q : Finset ℕ := ([0,2,3,5,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2942_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(0,16),(2,3),(2,5),(2,8),(2,10),(2,13),(2,16),(3,5),(3,8),(3,10),(3,13),(3,16),(5,8),(5,10),(5,13),(5,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2943_q : Finset ℕ := ([0,2,3,5,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2943_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,10),(0,14),(0,16),(2,3),(2,5),(2,8),(2,10),(2,14),(2,16),(3,5),(3,8),(3,10),(3,14),(3,16),(5,8),(5,10),(5,14),(5,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

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

noncomputable def certificate_2944_q : Finset ℕ := ([0,2,3,5,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2944_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,11),(0,12),(0,15),(2,3),(2,5),(2,8),(2,11),(2,12),(2,15),(3,5),(3,8),(3,11),(3,12),(3,15),(5,8),(5,11),(5,12),(5,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2945_q : Finset ℕ := ([0,2,3,5,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2945_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,11),(0,12),(0,16),(2,3),(2,5),(2,8),(2,11),(2,12),(2,16),(3,5),(3,8),(3,11),(3,12),(3,16),(5,8),(5,11),(5,12),(5,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2946_q : Finset ℕ := ([0,2,3,5,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2946_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(0,16),(2,3),(2,5),(2,8),(2,11),(2,13),(2,16),(3,5),(3,8),(3,11),(3,13),(3,16),(5,8),(5,11),(5,13),(5,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2947_q : Finset ℕ := ([0,2,3,5,8,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2947_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,11),(0,14),(0,16),(2,3),(2,5),(2,8),(2,11),(2,14),(2,16),(3,5),(3,8),(3,11),(3,14),(3,16),(5,8),(5,11),(5,14),(5,16),(8,11),(8,14),(8,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2948_q : Finset ℕ := ([0,2,3,5,8,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2948_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,8),(0,12),(0,13),(0,16),(2,3),(2,5),(2,8),(2,12),(2,13),(2,16),(3,5),(3,8),(3,12),(3,13),(3,16),(5,8),(5,12),(5,13),(5,16),(8,12),(8,13),(8,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2949_q : Finset ℕ := ([0,2,3,5,9,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2949_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,9),(0,10),(0,12),(0,16),(2,3),(2,5),(2,9),(2,10),(2,12),(2,16),(3,5),(3,9),(3,10),(3,12),(3,16),(5,9),(5,10),(5,12),(5,16),(9,10),(9,12),(9,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2950_q : Finset ℕ := ([0,2,3,5,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2950_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(0,16),(2,3),(2,5),(2,9),(2,10),(2,13),(2,16),(3,5),(3,9),(3,10),(3,13),(3,16),(5,9),(5,10),(5,13),(5,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2951_q : Finset ℕ := ([0,2,3,5,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2951_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,9),(0,11),(0,12),(0,15),(2,3),(2,5),(2,9),(2,11),(2,12),(2,15),(3,5),(3,9),(3,11),(3,12),(3,15),(5,9),(5,11),(5,12),(5,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2952_q : Finset ℕ := ([0,2,3,5,9,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2952_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,9),(0,11),(0,12),(0,16),(2,3),(2,5),(2,9),(2,11),(2,12),(2,16),(3,5),(3,9),(3,11),(3,12),(3,16),(5,9),(5,11),(5,12),(5,16),(9,11),(9,12),(9,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2953_q : Finset ℕ := ([0,2,3,5,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2953_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,9),(0,11),(0,13),(0,16),(2,3),(2,5),(2,9),(2,11),(2,13),(2,16),(3,5),(3,9),(3,11),(3,13),(3,16),(5,9),(5,11),(5,13),(5,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2954_q : Finset ℕ := ([0,2,3,5,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2954_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,9),(0,12),(0,13),(0,16),(2,3),(2,5),(2,9),(2,12),(2,13),(2,16),(3,5),(3,9),(3,12),(3,13),(3,16),(5,9),(5,12),(5,13),(5,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2955_q : Finset ℕ := ([0,2,3,5,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2955_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,3),(0,5),(0,10),(0,12),(0,13),(0,16),(2,3),(2,5),(2,10),(2,12),(2,13),(2,16),(3,5),(3,10),(3,12),(3,13),(3,16),(5,10),(5,12),(5,13),(5,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2956_q : Finset ℕ := ([0,2,3,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2956_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,7),(0,10),(0,11),(0,14),(2,3),(2,6),(2,7),(2,10),(2,11),(2,14),(3,6),(3,7),(3,10),(3,11),(3,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2957_q : Finset ℕ := ([0,2,3,6,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2957_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,6),(0,7),(0,10),(0,11),(0,15),(2,3),(2,6),(2,7),(2,10),(2,11),(2,15),(3,6),(3,7),(3,10),(3,11),(3,15),(6,7),(6,10),(6,11),(6,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2958_q : Finset ℕ := ([0,2,3,6,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2958_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,7),(0,10),(0,11),(0,16),(2,3),(2,6),(2,7),(2,10),(2,11),(2,16),(3,6),(3,7),(3,10),(3,11),(3,16),(6,7),(6,10),(6,11),(6,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2959_q : Finset ℕ := ([0,2,3,6,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2959_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,6),(0,7),(0,10),(0,12),(0,15),(2,3),(2,6),(2,7),(2,10),(2,12),(2,15),(3,6),(3,7),(3,10),(3,12),(3,15),(6,7),(6,10),(6,12),(6,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2960_q : Finset ℕ := ([0,2,3,6,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2960_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,7),(0,10),(0,12),(0,16),(2,3),(2,6),(2,7),(2,10),(2,12),(2,16),(3,6),(3,7),(3,10),(3,12),(3,16),(6,7),(6,10),(6,12),(6,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2961_q : Finset ℕ := ([0,2,3,6,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2961_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(0,16),(2,3),(2,6),(2,7),(2,10),(2,13),(2,16),(3,6),(3,7),(3,10),(3,13),(3,16),(6,7),(6,10),(6,13),(6,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2962_q : Finset ℕ := ([0,2,3,6,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2962_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,7),(0,11),(0,12),(0,16),(2,3),(2,6),(2,7),(2,11),(2,12),(2,16),(3,6),(3,7),(3,11),(3,12),(3,16),(6,7),(6,11),(6,12),(6,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2963_q : Finset ℕ := ([0,2,3,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2963_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,6),(0,8),(0,10),(0,12),(0,15),(2,3),(2,6),(2,8),(2,10),(2,12),(2,15),(3,6),(3,8),(3,10),(3,12),(3,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2964_q : Finset ℕ := ([0,2,3,6,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2964_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,8),(0,10),(0,12),(0,16),(2,3),(2,6),(2,8),(2,10),(2,12),(2,16),(3,6),(3,8),(3,10),(3,12),(3,16),(6,8),(6,10),(6,12),(6,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2965_q : Finset ℕ := ([0,2,3,6,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2965_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(0,16),(2,3),(2,6),(2,8),(2,10),(2,13),(2,16),(3,6),(3,8),(3,10),(3,13),(3,16),(6,8),(6,10),(6,13),(6,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2966_q : Finset ℕ := ([0,2,3,6,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2966_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,8),(0,11),(0,12),(0,16),(2,3),(2,6),(2,8),(2,11),(2,12),(2,16),(3,6),(3,8),(3,11),(3,12),(3,16),(6,8),(6,11),(6,12),(6,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2967_q : Finset ℕ := ([0,2,3,6,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2967_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,8),(0,11),(0,13),(0,16),(2,3),(2,6),(2,8),(2,11),(2,13),(2,16),(3,6),(3,8),(3,11),(3,13),(3,16),(6,8),(6,11),(6,13),(6,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2968_q : Finset ℕ := ([0,2,3,6,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2968_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,3),(0,6),(0,9),(0,10),(0,13),(0,16),(2,3),(2,6),(2,9),(2,10),(2,13),(2,16),(3,6),(3,9),(3,10),(3,13),(3,16),(6,9),(6,10),(6,13),(6,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2969_q : Finset ℕ := ([0,2,4,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2969_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,13),(2,4),(2,5),(2,7),(2,9),(2,10),(2,13),(4,5),(4,7),(4,9),(4,10),(4,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2970_q : Finset ℕ := ([0,2,4,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2970_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,14),(2,4),(2,5),(2,7),(2,9),(2,10),(2,14),(4,5),(4,7),(4,9),(4,10),(4,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2971_q : Finset ℕ := ([0,2,4,5,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2971_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,15),(2,4),(2,5),(2,7),(2,9),(2,10),(2,15),(4,5),(4,7),(4,9),(4,10),(4,15),(5,7),(5,9),(5,10),(5,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2972_q : Finset ℕ := ([0,2,4,5,7,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2972_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,16),(2,4),(2,5),(2,7),(2,9),(2,10),(2,16),(4,5),(4,7),(4,9),(4,10),(4,16),(5,7),(5,9),(5,10),(5,16),(7,9),(7,10),(7,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2973_q : Finset ℕ := ([0,2,4,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2973_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,13),(2,4),(2,5),(2,7),(2,9),(2,11),(2,13),(4,5),(4,7),(4,9),(4,11),(4,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2974_q : Finset ℕ := ([0,2,4,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2974_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,14),(2,4),(2,5),(2,7),(2,9),(2,11),(2,14),(4,5),(4,7),(4,9),(4,11),(4,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2975_q : Finset ℕ := ([0,2,4,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2975_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,15),(2,4),(2,5),(2,7),(2,9),(2,11),(2,15),(4,5),(4,7),(4,9),(4,11),(4,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

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

noncomputable def certificate_2976_q : Finset ℕ := ([0,2,4,5,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2976_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,16),(2,4),(2,5),(2,7),(2,9),(2,11),(2,16),(4,5),(4,7),(4,9),(4,11),(4,16),(5,7),(5,9),(5,11),(5,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2977_q : Finset ℕ := ([0,2,4,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2977_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(0,14),(2,4),(2,5),(2,7),(2,9),(2,12),(2,14),(4,5),(4,7),(4,9),(4,12),(4,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2978_q : Finset ℕ := ([0,2,4,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2978_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(0,15),(2,4),(2,5),(2,7),(2,9),(2,12),(2,15),(4,5),(4,7),(4,9),(4,12),(4,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2979_q : Finset ℕ := ([0,2,4,5,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2979_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(0,16),(2,4),(2,5),(2,7),(2,9),(2,12),(2,16),(4,5),(4,7),(4,9),(4,12),(4,16),(5,7),(5,9),(5,12),(5,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2980_q : Finset ℕ := ([0,2,4,5,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2980_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(0,15),(2,4),(2,5),(2,7),(2,9),(2,13),(2,15),(4,5),(4,7),(4,9),(4,13),(4,15),(5,7),(5,9),(5,13),(5,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2981_q : Finset ℕ := ([0,2,4,5,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2981_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(0,16),(2,4),(2,5),(2,7),(2,9),(2,13),(2,16),(4,5),(4,7),(4,9),(4,13),(4,16),(5,7),(5,9),(5,13),(5,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2982_q : Finset ℕ := ([0,2,4,5,7,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2982_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,9),(0,14),(0,16),(2,4),(2,5),(2,7),(2,9),(2,14),(2,16),(4,5),(4,7),(4,9),(4,14),(4,16),(5,7),(5,9),(5,14),(5,16),(7,9),(7,14),(7,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2983_q : Finset ℕ := ([0,2,4,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2983_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,10),(0,11),(0,14),(2,4),(2,5),(2,7),(2,10),(2,11),(2,14),(4,5),(4,7),(4,10),(4,11),(4,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2984_q : Finset ℕ := ([0,2,4,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2984_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,10),(0,11),(0,15),(2,4),(2,5),(2,7),(2,10),(2,11),(2,15),(4,5),(4,7),(4,10),(4,11),(4,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2985_q : Finset ℕ := ([0,2,4,5,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2985_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,10),(0,11),(0,16),(2,4),(2,5),(2,7),(2,10),(2,11),(2,16),(4,5),(4,7),(4,10),(4,11),(4,16),(5,7),(5,10),(5,11),(5,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2986_q : Finset ℕ := ([0,2,4,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2986_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(0,15),(2,4),(2,5),(2,7),(2,10),(2,12),(2,15),(4,5),(4,7),(4,10),(4,12),(4,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2987_q : Finset ℕ := ([0,2,4,5,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2987_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(0,16),(2,4),(2,5),(2,7),(2,10),(2,12),(2,16),(4,5),(4,7),(4,10),(4,12),(4,16),(5,7),(5,10),(5,12),(5,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2988_q : Finset ℕ := ([0,2,4,5,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2988_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(0,15),(2,4),(2,5),(2,7),(2,10),(2,13),(2,15),(4,5),(4,7),(4,10),(4,13),(4,15),(5,7),(5,10),(5,13),(5,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2989_q : Finset ℕ := ([0,2,4,5,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2989_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(0,16),(2,4),(2,5),(2,7),(2,10),(2,13),(2,16),(4,5),(4,7),(4,10),(4,13),(4,16),(5,7),(5,10),(5,13),(5,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2990_q : Finset ℕ := ([0,2,4,5,7,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2990_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,10),(0,14),(0,16),(2,4),(2,5),(2,7),(2,10),(2,14),(2,16),(4,5),(4,7),(4,10),(4,14),(4,16),(5,7),(5,10),(5,14),(5,16),(7,10),(7,14),(7,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2991_q : Finset ℕ := ([0,2,4,5,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2991_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,11),(0,12),(0,15),(2,4),(2,5),(2,7),(2,11),(2,12),(2,15),(4,5),(4,7),(4,11),(4,12),(4,15),(5,7),(5,11),(5,12),(5,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2992_q : Finset ℕ := ([0,2,4,5,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2992_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,11),(0,12),(0,16),(2,4),(2,5),(2,7),(2,11),(2,12),(2,16),(4,5),(4,7),(4,11),(4,12),(4,16),(5,7),(5,11),(5,12),(5,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2993_q : Finset ℕ := ([0,2,4,5,7,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2993_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(0,16),(2,4),(2,5),(2,7),(2,11),(2,13),(2,16),(4,5),(4,7),(4,11),(4,13),(4,16),(5,7),(5,11),(5,13),(5,16),(7,11),(7,13),(7,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2994_q : Finset ℕ := ([0,2,4,5,7,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2994_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,7),(0,12),(0,13),(0,16),(2,4),(2,5),(2,7),(2,12),(2,13),(2,16),(4,5),(4,7),(4,12),(4,13),(4,16),(5,7),(5,12),(5,13),(5,16),(7,12),(7,13),(7,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2995_q : Finset ℕ := ([0,2,4,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2995_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(0,15),(2,4),(2,5),(2,8),(2,9),(2,12),(2,15),(4,5),(4,8),(4,9),(4,12),(4,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2996_q : Finset ℕ := ([0,2,4,5,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2996_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(0,16),(2,4),(2,5),(2,8),(2,9),(2,12),(2,16),(4,5),(4,8),(4,9),(4,12),(4,16),(5,8),(5,9),(5,12),(5,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2997_q : Finset ℕ := ([0,2,4,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2997_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,8),(0,10),(0,12),(0,15),(2,4),(2,5),(2,8),(2,10),(2,12),(2,15),(4,5),(4,8),(4,10),(4,12),(4,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2998_q : Finset ℕ := ([0,2,4,5,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2998_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,8),(0,10),(0,12),(0,16),(2,4),(2,5),(2,8),(2,10),(2,12),(2,16),(4,5),(4,8),(4,10),(4,12),(4,16),(5,8),(5,10),(5,12),(5,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2999_q : Finset ℕ := ([0,2,4,5,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2999_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(0,16),(2,4),(2,5),(2,8),(2,10),(2,13),(2,16),(4,5),(4,8),(4,10),(4,13),(4,16),(5,8),(5,10),(5,13),(5,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3000_q : Finset ℕ := ([0,2,4,5,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3000_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,5),(0,8),(0,11),(0,12),(0,16),(2,4),(2,5),(2,8),(2,11),(2,12),(2,16),(4,5),(4,8),(4,11),(4,12),(4,16),(5,8),(5,11),(5,12),(5,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3001_q : Finset ℕ := ([0,2,4,6,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_3001_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,13),(2,4),(2,6),(2,7),(2,9),(2,11),(2,13),(4,6),(4,7),(4,9),(4,11),(4,13),(6,7),(6,9),(6,11),(6,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_3002_q : Finset ℕ := ([0,2,4,6,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_3002_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,14),(2,4),(2,6),(2,7),(2,9),(2,11),(2,14),(4,6),(4,7),(4,9),(4,11),(4,14),(6,7),(6,9),(6,11),(6,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_3003_q : Finset ℕ := ([0,2,4,6,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_3003_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,15),(2,4),(2,6),(2,7),(2,9),(2,11),(2,15),(4,6),(4,7),(4,9),(4,11),(4,15),(6,7),(6,9),(6,11),(6,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_3004_q : Finset ℕ := ([0,2,4,6,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_3004_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,16),(2,4),(2,6),(2,7),(2,9),(2,11),(2,16),(4,6),(4,7),(4,9),(4,11),(4,16),(6,7),(6,9),(6,11),(6,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_3005_q : Finset ℕ := ([0,2,4,6,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_3005_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(0,14),(2,4),(2,6),(2,7),(2,9),(2,12),(2,14),(4,6),(4,7),(4,9),(4,12),(4,14),(6,7),(6,9),(6,12),(6,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_3006_q : Finset ℕ := ([0,2,4,6,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_3006_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(0,15),(2,4),(2,6),(2,7),(2,9),(2,12),(2,15),(4,6),(4,7),(4,9),(4,12),(4,15),(6,7),(6,9),(6,12),(6,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_3007_q : Finset ℕ := ([0,2,4,6,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_3007_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(0,16),(2,4),(2,6),(2,7),(2,9),(2,12),(2,16),(4,6),(4,7),(4,9),(4,12),(4,16),(6,7),(6,9),(6,12),(6,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

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

noncomputable def certificate_3008_q : Finset ℕ := ([0,2,4,6,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_3008_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(0,15),(2,4),(2,6),(2,7),(2,9),(2,13),(2,15),(4,6),(4,7),(4,9),(4,13),(4,15),(6,7),(6,9),(6,13),(6,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_3009_q : Finset ℕ := ([0,2,4,6,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_3009_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(0,16),(2,4),(2,6),(2,7),(2,9),(2,13),(2,16),(4,6),(4,7),(4,9),(4,13),(4,16),(6,7),(6,9),(6,13),(6,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_3010_q : Finset ℕ := ([0,2,4,6,7,9,14,16] : List ℕ).toFinset
noncomputable def certificate_3010_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,9),(0,14),(0,16),(2,4),(2,6),(2,7),(2,9),(2,14),(2,16),(4,6),(4,7),(4,9),(4,14),(4,16),(6,7),(6,9),(6,14),(6,16),(7,9),(7,14),(7,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_3011_q : Finset ℕ := ([0,2,4,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_3011_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,10),(0,11),(0,14),(2,4),(2,6),(2,7),(2,10),(2,11),(2,14),(4,6),(4,7),(4,10),(4,11),(4,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_3012_q : Finset ℕ := ([0,2,4,6,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_3012_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,10),(0,11),(0,15),(2,4),(2,6),(2,7),(2,10),(2,11),(2,15),(4,6),(4,7),(4,10),(4,11),(4,15),(6,7),(6,10),(6,11),(6,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_3013_q : Finset ℕ := ([0,2,4,6,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_3013_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,10),(0,11),(0,16),(2,4),(2,6),(2,7),(2,10),(2,11),(2,16),(4,6),(4,7),(4,10),(4,11),(4,16),(6,7),(6,10),(6,11),(6,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_3014_q : Finset ℕ := ([0,2,4,6,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_3014_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,10),(0,12),(0,15),(2,4),(2,6),(2,7),(2,10),(2,12),(2,15),(4,6),(4,7),(4,10),(4,12),(4,15),(6,7),(6,10),(6,12),(6,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_3015_q : Finset ℕ := ([0,2,4,6,7,10,12,16] : List ℕ).toFinset
noncomputable def certificate_3015_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,10),(0,12),(0,16),(2,4),(2,6),(2,7),(2,10),(2,12),(2,16),(4,6),(4,7),(4,10),(4,12),(4,16),(6,7),(6,10),(6,12),(6,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_3016_q : Finset ℕ := ([0,2,4,6,7,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3016_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(0,16),(2,4),(2,6),(2,7),(2,10),(2,13),(2,16),(4,6),(4,7),(4,10),(4,13),(4,16),(6,7),(6,10),(6,13),(6,16),(7,10),(7,13),(7,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3017_q : Finset ℕ := ([0,2,4,6,7,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3017_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,7),(0,11),(0,12),(0,16),(2,4),(2,6),(2,7),(2,11),(2,12),(2,16),(4,6),(4,7),(4,11),(4,12),(4,16),(6,7),(6,11),(6,12),(6,16),(7,11),(7,12),(7,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3018_q : Finset ℕ := ([0,2,4,6,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_3018_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,9),(0,11),(0,14),(2,4),(2,6),(2,8),(2,9),(2,11),(2,14),(4,6),(4,8),(4,9),(4,11),(4,14),(6,8),(6,9),(6,11),(6,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_3019_q : Finset ℕ := ([0,2,4,6,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_3019_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,9),(0,11),(0,15),(2,4),(2,6),(2,8),(2,9),(2,11),(2,15),(4,6),(4,8),(4,9),(4,11),(4,15),(6,8),(6,9),(6,11),(6,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_3020_q : Finset ℕ := ([0,2,4,6,8,9,11,16] : List ℕ).toFinset
noncomputable def certificate_3020_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,9),(0,11),(0,16),(2,4),(2,6),(2,8),(2,9),(2,11),(2,16),(4,6),(4,8),(4,9),(4,11),(4,16),(6,8),(6,9),(6,11),(6,16),(8,9),(8,11),(8,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_3021_q : Finset ℕ := ([0,2,4,6,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_3021_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(0,15),(2,4),(2,6),(2,8),(2,9),(2,12),(2,15),(4,6),(4,8),(4,9),(4,12),(4,15),(6,8),(6,9),(6,12),(6,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_3022_q : Finset ℕ := ([0,2,4,6,8,9,12,16] : List ℕ).toFinset
noncomputable def certificate_3022_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(0,16),(2,4),(2,6),(2,8),(2,9),(2,12),(2,16),(4,6),(4,8),(4,9),(4,12),(4,16),(6,8),(6,9),(6,12),(6,16),(8,9),(8,12),(8,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_3023_q : Finset ℕ := ([0,2,4,6,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_3023_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,11),(0,14),(2,4),(2,6),(2,8),(2,10),(2,11),(2,14),(4,6),(4,8),(4,10),(4,11),(4,14),(6,8),(6,10),(6,11),(6,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_3024_q : Finset ℕ := ([0,2,4,6,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_3024_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,10),(0,11),(0,15),(2,4),(2,6),(2,8),(2,10),(2,11),(2,15),(4,6),(4,8),(4,10),(4,11),(4,15),(6,8),(6,10),(6,11),(6,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_3025_q : Finset ℕ := ([0,2,4,6,8,10,11,16] : List ℕ).toFinset
noncomputable def certificate_3025_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,10),(0,11),(0,16),(2,4),(2,6),(2,8),(2,10),(2,11),(2,16),(4,6),(4,8),(4,10),(4,11),(4,16),(6,8),(6,10),(6,11),(6,16),(8,10),(8,11),(8,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_3026_q : Finset ℕ := ([0,2,4,6,8,10,12,14] : List ℕ).toFinset
noncomputable def certificate_3026_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(0,14),(2,4),(2,6),(2,8),(2,10),(2,12),(2,14),(4,6),(4,8),(4,10),(4,12),(4,14),(6,8),(6,10),(6,12),(6,14),(8,10),(8,12),(8,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_3027_q : Finset ℕ := ([0,2,4,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_3027_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(0,15),(2,4),(2,6),(2,8),(2,10),(2,12),(2,15),(4,6),(4,8),(4,10),(4,12),(4,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_3028_q : Finset ℕ := ([0,2,4,6,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_3028_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(0,16),(2,4),(2,6),(2,8),(2,10),(2,12),(2,16),(4,6),(4,8),(4,10),(4,12),(4,16),(6,8),(6,10),(6,12),(6,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_3029_q : Finset ℕ := ([0,2,4,6,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_3029_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(0,15),(2,4),(2,6),(2,8),(2,10),(2,13),(2,15),(4,6),(4,8),(4,10),(4,13),(4,15),(6,8),(6,10),(6,13),(6,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_3030_q : Finset ℕ := ([0,2,4,6,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3030_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(0,16),(2,4),(2,6),(2,8),(2,10),(2,13),(2,16),(4,6),(4,8),(4,10),(4,13),(4,16),(6,8),(6,10),(6,13),(6,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3031_q : Finset ℕ := ([0,2,4,6,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_3031_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,10),(0,14),(0,16),(2,4),(2,6),(2,8),(2,10),(2,14),(2,16),(4,6),(4,8),(4,10),(4,14),(4,16),(6,8),(6,10),(6,14),(6,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_3032_q : Finset ℕ := ([0,2,4,6,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3032_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,11),(0,12),(0,15),(2,4),(2,6),(2,8),(2,11),(2,12),(2,15),(4,6),(4,8),(4,11),(4,12),(4,15),(6,8),(6,11),(6,12),(6,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3033_q : Finset ℕ := ([0,2,4,6,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3033_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,11),(0,12),(0,16),(2,4),(2,6),(2,8),(2,11),(2,12),(2,16),(4,6),(4,8),(4,11),(4,12),(4,16),(6,8),(6,11),(6,12),(6,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3034_q : Finset ℕ := ([0,2,4,6,8,11,13,15] : List ℕ).toFinset
noncomputable def certificate_3034_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(0,15),(2,4),(2,6),(2,8),(2,11),(2,13),(2,15),(4,6),(4,8),(4,11),(4,13),(4,15),(6,8),(6,11),(6,13),(6,15),(8,11),(8,13),(8,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_3035_q : Finset ℕ := ([0,2,4,6,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3035_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(0,16),(2,4),(2,6),(2,8),(2,11),(2,13),(2,16),(4,6),(4,8),(4,11),(4,13),(4,16),(6,8),(6,11),(6,13),(6,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3036_q : Finset ℕ := ([0,2,4,6,8,11,14,16] : List ℕ).toFinset
noncomputable def certificate_3036_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,11),(0,14),(0,16),(2,4),(2,6),(2,8),(2,11),(2,14),(2,16),(4,6),(4,8),(4,11),(4,14),(4,16),(6,8),(6,11),(6,14),(6,16),(8,11),(8,14),(8,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_3037_q : Finset ℕ := ([0,2,4,6,8,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3037_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,12),(0,13),(0,16),(2,4),(2,6),(2,8),(2,12),(2,13),(2,16),(4,6),(4,8),(4,12),(4,13),(4,16),(6,8),(6,12),(6,13),(6,16),(8,12),(8,13),(8,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3038_q : Finset ℕ := ([0,2,4,6,8,12,14,16] : List ℕ).toFinset
noncomputable def certificate_3038_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,8),(0,12),(0,14),(0,16),(2,4),(2,6),(2,8),(2,12),(2,14),(2,16),(4,6),(4,8),(4,12),(4,14),(4,16),(6,8),(6,12),(6,14),(6,16),(8,12),(8,14),(8,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_3039_q : Finset ℕ := ([0,2,4,6,9,10,12,15] : List ℕ).toFinset
noncomputable def certificate_3039_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,9),(0,10),(0,12),(0,15),(2,4),(2,6),(2,9),(2,10),(2,12),(2,15),(4,6),(4,9),(4,10),(4,12),(4,15),(6,9),(6,10),(6,12),(6,15),(9,10),(9,12),(9,15),(10,12),(10,15),(12,15)]

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

noncomputable def certificate_3040_q : Finset ℕ := ([0,2,4,6,9,10,12,16] : List ℕ).toFinset
noncomputable def certificate_3040_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,10),(0,12),(0,16),(2,4),(2,6),(2,9),(2,10),(2,12),(2,16),(4,6),(4,9),(4,10),(4,12),(4,16),(6,9),(6,10),(6,12),(6,16),(9,10),(9,12),(9,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_3041_q : Finset ℕ := ([0,2,4,6,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3041_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(0,16),(2,4),(2,6),(2,9),(2,10),(2,13),(2,16),(4,6),(4,9),(4,10),(4,13),(4,16),(6,9),(6,10),(6,13),(6,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3042_q : Finset ℕ := ([0,2,4,6,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3042_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,9),(0,11),(0,12),(0,15),(2,4),(2,6),(2,9),(2,11),(2,12),(2,15),(4,6),(4,9),(4,11),(4,12),(4,15),(6,9),(6,11),(6,12),(6,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3043_q : Finset ℕ := ([0,2,4,6,9,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3043_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,11),(0,12),(0,16),(2,4),(2,6),(2,9),(2,11),(2,12),(2,16),(4,6),(4,9),(4,11),(4,12),(4,16),(6,9),(6,11),(6,12),(6,16),(9,11),(9,12),(9,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3044_q : Finset ℕ := ([0,2,4,6,9,11,13,15] : List ℕ).toFinset
noncomputable def certificate_3044_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(0,15),(2,4),(2,6),(2,9),(2,11),(2,13),(2,15),(4,6),(4,9),(4,11),(4,13),(4,15),(6,9),(6,11),(6,13),(6,15),(9,11),(9,13),(9,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_3045_q : Finset ℕ := ([0,2,4,6,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3045_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(0,16),(2,4),(2,6),(2,9),(2,11),(2,13),(2,16),(4,6),(4,9),(4,11),(4,13),(4,16),(6,9),(6,11),(6,13),(6,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3046_q : Finset ℕ := ([0,2,4,6,9,11,14,16] : List ℕ).toFinset
noncomputable def certificate_3046_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,11),(0,14),(0,16),(2,4),(2,6),(2,9),(2,11),(2,14),(2,16),(4,6),(4,9),(4,11),(4,14),(4,16),(6,9),(6,11),(6,14),(6,16),(9,11),(9,14),(9,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_3047_q : Finset ℕ := ([0,2,4,6,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3047_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,12),(0,13),(0,16),(2,4),(2,6),(2,9),(2,12),(2,13),(2,16),(4,6),(4,9),(4,12),(4,13),(4,16),(6,9),(6,12),(6,13),(6,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3048_q : Finset ℕ := ([0,2,4,6,9,12,14,16] : List ℕ).toFinset
noncomputable def certificate_3048_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,9),(0,12),(0,14),(0,16),(2,4),(2,6),(2,9),(2,12),(2,14),(2,16),(4,6),(4,9),(4,12),(4,14),(4,16),(6,9),(6,12),(6,14),(6,16),(9,12),(9,14),(9,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_3049_q : Finset ℕ := ([0,2,4,6,10,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3049_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,10),(0,11),(0,13),(0,16),(2,4),(2,6),(2,10),(2,11),(2,13),(2,16),(4,6),(4,10),(4,11),(4,13),(4,16),(6,10),(6,11),(6,13),(6,16),(10,11),(10,13),(10,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3050_q : Finset ℕ := ([0,2,4,6,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3050_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,10),(0,12),(0,13),(0,16),(2,4),(2,6),(2,10),(2,12),(2,13),(2,16),(4,6),(4,10),(4,12),(4,13),(4,16),(6,10),(6,12),(6,13),(6,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3051_q : Finset ℕ := ([0,2,4,6,10,12,14,16] : List ℕ).toFinset
noncomputable def certificate_3051_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,6),(0,10),(0,12),(0,14),(0,16),(2,4),(2,6),(2,10),(2,12),(2,14),(2,16),(4,6),(4,10),(4,12),(4,14),(4,16),(6,10),(6,12),(6,14),(6,16),(10,12),(10,14),(10,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_3052_q : Finset ℕ := ([0,2,4,7,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_3052_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,8),(0,10),(0,12),(0,15),(2,4),(2,7),(2,8),(2,10),(2,12),(2,15),(4,7),(4,8),(4,10),(4,12),(4,15),(7,8),(7,10),(7,12),(7,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_3053_q : Finset ℕ := ([0,2,4,7,8,10,12,16] : List ℕ).toFinset
noncomputable def certificate_3053_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,8),(0,10),(0,12),(0,16),(2,4),(2,7),(2,8),(2,10),(2,12),(2,16),(4,7),(4,8),(4,10),(4,12),(4,16),(7,8),(7,10),(7,12),(7,16),(8,10),(8,12),(8,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_3054_q : Finset ℕ := ([0,2,4,7,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_3054_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(0,15),(2,4),(2,7),(2,8),(2,10),(2,13),(2,15),(4,7),(4,8),(4,10),(4,13),(4,15),(7,8),(7,10),(7,13),(7,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_3055_q : Finset ℕ := ([0,2,4,7,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3055_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(0,16),(2,4),(2,7),(2,8),(2,10),(2,13),(2,16),(4,7),(4,8),(4,10),(4,13),(4,16),(7,8),(7,10),(7,13),(7,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3056_q : Finset ℕ := ([0,2,4,7,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_3056_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,8),(0,10),(0,14),(0,16),(2,4),(2,7),(2,8),(2,10),(2,14),(2,16),(4,7),(4,8),(4,10),(4,14),(4,16),(7,8),(7,10),(7,14),(7,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_3057_q : Finset ℕ := ([0,2,4,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3057_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,8),(0,11),(0,12),(0,15),(2,4),(2,7),(2,8),(2,11),(2,12),(2,15),(4,7),(4,8),(4,11),(4,12),(4,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3058_q : Finset ℕ := ([0,2,4,7,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3058_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,8),(0,11),(0,12),(0,16),(2,4),(2,7),(2,8),(2,11),(2,12),(2,16),(4,7),(4,8),(4,11),(4,12),(4,16),(7,8),(7,11),(7,12),(7,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3059_q : Finset ℕ := ([0,2,4,7,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3059_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,8),(0,11),(0,13),(0,16),(2,4),(2,7),(2,8),(2,11),(2,13),(2,16),(4,7),(4,8),(4,11),(4,13),(4,16),(7,8),(7,11),(7,13),(7,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3060_q : Finset ℕ := ([0,2,4,7,9,10,12,15] : List ℕ).toFinset
noncomputable def certificate_3060_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,9),(0,10),(0,12),(0,15),(2,4),(2,7),(2,9),(2,10),(2,12),(2,15),(4,7),(4,9),(4,10),(4,12),(4,15),(7,9),(7,10),(7,12),(7,15),(9,10),(9,12),(9,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_3061_q : Finset ℕ := ([0,2,4,7,9,10,12,16] : List ℕ).toFinset
noncomputable def certificate_3061_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,10),(0,12),(0,16),(2,4),(2,7),(2,9),(2,10),(2,12),(2,16),(4,7),(4,9),(4,10),(4,12),(4,16),(7,9),(7,10),(7,12),(7,16),(9,10),(9,12),(9,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_3062_q : Finset ℕ := ([0,2,4,7,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3062_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(0,16),(2,4),(2,7),(2,9),(2,10),(2,13),(2,16),(4,7),(4,9),(4,10),(4,13),(4,16),(7,9),(7,10),(7,13),(7,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3063_q : Finset ℕ := ([0,2,4,7,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3063_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,9),(0,11),(0,12),(0,15),(2,4),(2,7),(2,9),(2,11),(2,12),(2,15),(4,7),(4,9),(4,11),(4,12),(4,15),(7,9),(7,11),(7,12),(7,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3064_q : Finset ℕ := ([0,2,4,7,9,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3064_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,11),(0,12),(0,16),(2,4),(2,7),(2,9),(2,11),(2,12),(2,16),(4,7),(4,9),(4,11),(4,12),(4,16),(7,9),(7,11),(7,12),(7,16),(9,11),(9,12),(9,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3065_q : Finset ℕ := ([0,2,4,7,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3065_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,11),(0,13),(0,16),(2,4),(2,7),(2,9),(2,11),(2,13),(2,16),(4,7),(4,9),(4,11),(4,13),(4,16),(7,9),(7,11),(7,13),(7,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3066_q : Finset ℕ := ([0,2,4,7,9,11,14,16] : List ℕ).toFinset
noncomputable def certificate_3066_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,11),(0,14),(0,16),(2,4),(2,7),(2,9),(2,11),(2,14),(2,16),(4,7),(4,9),(4,11),(4,14),(4,16),(7,9),(7,11),(7,14),(7,16),(9,11),(9,14),(9,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_3067_q : Finset ℕ := ([0,2,4,7,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3067_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,12),(0,13),(0,16),(2,4),(2,7),(2,9),(2,12),(2,13),(2,16),(4,7),(4,9),(4,12),(4,13),(4,16),(7,9),(7,12),(7,13),(7,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3068_q : Finset ℕ := ([0,2,4,7,9,12,14,16] : List ℕ).toFinset

noncomputable def certificate_3069_q : Finset ℕ := ([0,2,4,7,10,11,13,16] : List ℕ).toFinset

end CycleClique

end OAI
end


