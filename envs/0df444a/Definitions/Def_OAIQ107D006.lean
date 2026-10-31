-- Prove2me | Definitions.Def_OAIQ107D006
-- name    : OAIQ107D006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:39:02.432058+00:00
-- url     : https://prove2.me/theorems/d3b0408f-dda9-44b6-a261-ca75fffcfdb2
-- title:
--   Definitions bundle OAIQ107D006 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1427 declarations of OpenAI's Lean: 1427 definitions. The definitions and types are `OAI.CycleClique.certificate_3068_edges`, `OAI.CycleClique.certificate_3069_edges`, `OAI.CycleClique.certificate_306_edges`, `OAI.CycleClique.certificate_306_q`, `OAI.CycleClique.certificate_3070_edges`, `OAI.CycleClique.certificate_3070_q`, `OAI.CycleClique.certificate_3071_edges`, `OAI.CycleClique.certificate_3071_q`, `OAI.CycleClique.certificate_3072_edges`, `OAI.CycleClique.certificate_3072_q`, `OAI.CycleClique.certificate_3073_edges`, `OAI.CycleClique.certificate_3073_q`, `OAI.CycleClique.certificate_3074_edges`, `OAI.CycleClique.certificate_3074_q`, `OAI.CycleClique.certificate_3075_edges`, `OAI.CycleClique.certificate_3075_q`, `OAI.CycleClique.certificate_3076_edges`, `OAI.CycleClique.certificate_3076_q`, `OAI.CycleClique.certificate_3077_edges`, `OAI.CycleClique.certificate_3077_q`, `OAI.CycleClique.certificate_3078_edges`, `OAI.CycleClique.certificate_3078_q`, `OAI.CycleClique.certificate_3079_edges`, `OAI.CycleClique.certificate_3079_q`, `OAI.CycleClique.certificate_307_edges`, `OAI.CycleClique.certificate_307_q`, `OAI.CycleClique.certificate_3080_edges`, `OAI.CycleClique.certificate_3080_q`, `OAI.CycleClique.certificate_3081_edges`, `OAI.CycleClique.certificate_3081_q`, `OAI.CycleClique.certificate_3082_edges`, `OAI.CycleClique.certificate_3082_q`, `OAI.CycleClique.certificate_3083_edges`, `OAI.CycleClique.certificate_3083_q`, `OAI.CycleClique.certificate_3084_edges`, `OAI.CycleClique.certificate_3084_q`, `OAI.CycleClique.certificate_3085_edges`, `OAI.CycleClique.certificate_3085_q`, `OAI.CycleClique.certificate_3086_edges`, `OAI.CycleClique.certificate_3086_q` and 1387 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates002`, `Ramsey_CycleClique_Certificates003`, `Ramsey_CycleClique_Certificates010`, `Ramsey_CycleClique_Certificates011`, `Ramsey_CycleClique_Certificates012`, `Ramsey_CycleClique_Certificates013`, `Ramsey_CycleClique_Certificates014`, `Ramsey_CycleClique_Certificates015`, `Ramsey_CycleClique_Certificates016`, `Ramsey_CycleClique_Certificates017`, `Ramsey_CycleClique_Certificates018`, `Ramsey_CycleClique_Certificates019`, `Ramsey_CycleClique_Certificates020`, `Ramsey_CycleClique_Certificates021`, `Ramsey_CycleClique_Certificates022`, `Ramsey_CycleClique_Certificates023`, `Ramsey_CycleClique_Certificates024`, `Ramsey_CycleClique_Certificates025`, `Ramsey_CycleClique_Certificates026`, `Ramsey_CycleClique_Certificates096`, `Ramsey_CycleClique_Certificates097`, `Ramsey_CycleClique_CompactDecisions`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D102`, `OAIQ107D104`, `OAIQ107D105`, `OAIQ107D106`, `OAIQ107D107`, `OAIQ107D108`, `OAIQ107D109`, `OAIQ107D110`, `OAIQ107D111`, `OAIQ107D113` and `OAIQ107D119`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CompactDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def compactChainLabels (R : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: L => R a b && compactChainLabels R (b :: L)

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_3_q : Finset ℕ := ([0,2,4] : List ℕ).toFinset

noncomputable def certificate_3_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(0,2),(0,4),(2,4)]

noncomputable def certificate_3_E : List (ℕ × ℕ) := certificate_3_edges

noncomputable def certificate_3_part_1_E : List (ℕ × ℕ) := certificate_3_E

noncomputable def certificate_4_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_4_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_5_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_5_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_6_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_6_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_7_q : Finset ℕ := ([0,1,2] : List ℕ).toFinset
noncomputable def certificate_7_edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]

noncomputable def certificate_30_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_31_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_31_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

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

noncomputable def certificate_32_q : Finset ℕ := ([0,1,2,5] : List ℕ).toFinset
noncomputable def certificate_32_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(0,1),(0,2),(0,5),(1,2),(1,5),(2,5)]

noncomputable def certificate_33_q : Finset ℕ := ([0,1,2,6] : List ℕ).toFinset

noncomputable def certificate_33_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,6),(1,2),(1,6),(2,6)]

noncomputable def certificate_33_E : List (ℕ × ℕ) := certificate_33_edges

noncomputable def certificate_33_part_1_E : List (ℕ × ℕ) := certificate_33_E

noncomputable def certificate_33_part_2_E : List (ℕ × ℕ) := certificate_33_part_1_E

noncomputable def certificate_33_part_4_E : List (ℕ × ℕ) := certificate_33_part_2_E

noncomputable def certificate_33_part_5_E : List (ℕ × ℕ) := certificate_33_part_4_E

noncomputable def certificate_33_part_6_E : List (ℕ × ℕ) := certificate_33_part_5_E

noncomputable def certificate_33_part_9_E : List (ℕ × ℕ) := certificate_33_part_6_E

noncomputable def certificate_33_part_11_E : List (ℕ × ℕ) := certificate_33_part_9_E

noncomputable def certificate_33_part_12_E : List (ℕ × ℕ) := certificate_33_part_11_E

noncomputable def certificate_34_q : Finset ℕ := ([0,1,3,5] : List ℕ).toFinset
noncomputable def certificate_34_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,3),(0,5),(1,3),(1,5),(3,5)]

noncomputable def certificate_35_q : Finset ℕ := ([0,1,3,6] : List ℕ).toFinset
noncomputable def certificate_35_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(0,1),(0,3),(0,6),(1,3),(1,6),(3,6)]

noncomputable def certificate_36_q : Finset ℕ := ([0,2,3,5] : List ℕ).toFinset
noncomputable def certificate_36_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(0,2),(0,3),(0,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_37_q : Finset ℕ := ([0,2,3,6] : List ℕ).toFinset
noncomputable def certificate_37_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(0,2),(0,3),(0,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_38_q : Finset ℕ := ([0,2,4,6] : List ℕ).toFinset
noncomputable def certificate_38_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,2),(0,4),(0,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_39_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_39_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_40_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_40_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_41_q : Finset ℕ := ([0,1,2,3,6] : List ℕ).toFinset
noncomputable def certificate_41_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_42_q : Finset ℕ := ([0,1,2,4,6] : List ℕ).toFinset
noncomputable def certificate_42_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,4),(0,6),(1,2),(1,4),(1,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_43_q : Finset ℕ := ([0,1,3,4,6] : List ℕ).toFinset
noncomputable def certificate_43_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(0,1),(0,3),(0,4),(0,6),(1,3),(1,4),(1,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_44_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_44_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_45_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_45_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_46_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_46_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_47_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_47_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_48_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_48_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_49_q : Finset ℕ := ([0,1,2,5] : List ℕ).toFinset
noncomputable def certificate_49_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(0,1),(0,2),(0,5),(1,2),(1,5),(2,5)]

noncomputable def certificate_50_q : Finset ℕ := ([0,1,2,6] : List ℕ).toFinset

noncomputable def certificate_50_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,6),(1,2),(1,6),(2,6)]

noncomputable def certificate_50_E : List (ℕ × ℕ) := certificate_50_edges

noncomputable def certificate_50_part_1_E : List (ℕ × ℕ) := certificate_50_E

noncomputable def certificate_50_part_2_E : List (ℕ × ℕ) := certificate_50_part_1_E

noncomputable def certificate_50_part_3_E : List (ℕ × ℕ) := certificate_50_part_2_E

noncomputable def certificate_50_part_4_E : List (ℕ × ℕ) := certificate_50_part_3_E

noncomputable def certificate_50_part_5_E : List (ℕ × ℕ) := certificate_50_part_4_E

noncomputable def certificate_50_part_6_E : List (ℕ × ℕ) := certificate_50_part_5_E

noncomputable def certificate_51_q : Finset ℕ := ([0,1,2,7] : List ℕ).toFinset

noncomputable def certificate_51_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,7),(1,2),(1,7),(2,7)]

noncomputable def certificate_51_E : List (ℕ × ℕ) := certificate_51_edges

noncomputable def certificate_51_part_1_E : List (ℕ × ℕ) := certificate_51_E

noncomputable def certificate_51_part_2_E : List (ℕ × ℕ) := certificate_51_part_1_E

noncomputable def certificate_51_part_4_E : List (ℕ × ℕ) := certificate_51_part_2_E

noncomputable def certificate_51_part_6_E : List (ℕ × ℕ) := certificate_51_part_4_E

noncomputable def certificate_51_part_7_E : List (ℕ × ℕ) := certificate_51_part_6_E

noncomputable def certificate_51_part_9_E : List (ℕ × ℕ) := certificate_51_part_7_E

noncomputable def certificate_51_part_11_E : List (ℕ × ℕ) := certificate_51_part_9_E

noncomputable def certificate_52_q : Finset ℕ := ([0,1,3,5] : List ℕ).toFinset
noncomputable def certificate_52_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,3),(0,5),(1,3),(1,5),(3,5)]

noncomputable def certificate_53_q : Finset ℕ := ([0,1,3,6] : List ℕ).toFinset
noncomputable def certificate_53_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(0,1),(0,3),(0,6),(1,3),(1,6),(3,6)]

noncomputable def certificate_54_q : Finset ℕ := ([0,1,3,7] : List ℕ).toFinset
noncomputable def certificate_54_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,3),(0,7),(1,3),(1,7),(3,7)]

noncomputable def certificate_55_q : Finset ℕ := ([0,1,4,7] : List ℕ).toFinset
noncomputable def certificate_55_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,4),(0,7),(1,4),(1,7),(4,7)]

noncomputable def certificate_56_q : Finset ℕ := ([0,2,3,5] : List ℕ).toFinset
noncomputable def certificate_56_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(0,2),(0,3),(0,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_57_q : Finset ℕ := ([0,2,3,6] : List ℕ).toFinset
noncomputable def certificate_57_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(0,2),(0,3),(0,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_58_q : Finset ℕ := ([0,2,3,7] : List ℕ).toFinset

noncomputable def certificate_58_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(0,2),(0,3),(0,7),(2,3),(2,7),(3,7)]

noncomputable def certificate_58_E : List (ℕ × ℕ) := certificate_58_edges

noncomputable def certificate_58_part_1_E : List (ℕ × ℕ) := certificate_58_E

noncomputable def certificate_58_part_2_E : List (ℕ × ℕ) := certificate_58_part_1_E

noncomputable def certificate_58_part_4_E : List (ℕ × ℕ) := certificate_58_part_2_E

noncomputable def certificate_58_part_5_E : List (ℕ × ℕ) := certificate_58_part_4_E

noncomputable def certificate_58_part_7_E : List (ℕ × ℕ) := certificate_58_part_5_E

noncomputable def certificate_58_part_8_E : List (ℕ × ℕ) := certificate_58_part_7_E

noncomputable def certificate_58_part_9_E : List (ℕ × ℕ) := certificate_58_part_8_E

noncomputable def certificate_59_q : Finset ℕ := ([0,2,4,6] : List ℕ).toFinset
noncomputable def certificate_59_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(0,2),(0,4),(0,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_60_q : Finset ℕ := ([0,2,4,7] : List ℕ).toFinset
noncomputable def certificate_60_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,2),(0,4),(0,7),(2,4),(2,7),(4,7)]

noncomputable def certificate_61_q : Finset ℕ := ([0,2,5,7] : List ℕ).toFinset
noncomputable def certificate_61_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,2),(0,5),(0,7),(2,5),(2,7),(5,7)]

noncomputable def certificate_62_q : Finset ℕ := ([0,3,4,7] : List ℕ).toFinset
noncomputable def certificate_62_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(0,3),(0,4),(0,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_63_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_63_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_64_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_64_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_65_q : Finset ℕ := ([0,1,2,3,6] : List ℕ).toFinset
noncomputable def certificate_65_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_66_q : Finset ℕ := ([0,1,2,3,7] : List ℕ).toFinset

noncomputable def certificate_66_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,7),(1,2),(1,3),(1,7),(2,3),(2,7),(3,7)]

noncomputable def certificate_66_E : List (ℕ × ℕ) := certificate_66_edges

noncomputable def certificate_66_part_1_E : List (ℕ × ℕ) := certificate_66_E

noncomputable def certificate_66_part_2_E : List (ℕ × ℕ) := certificate_66_part_1_E

noncomputable def certificate_66_part_4_E : List (ℕ × ℕ) := certificate_66_part_2_E

noncomputable def certificate_66_part_6_E : List (ℕ × ℕ) := certificate_66_part_4_E

noncomputable def certificate_66_part_7_E : List (ℕ × ℕ) := certificate_66_part_6_E

noncomputable def certificate_66_part_9_E : List (ℕ × ℕ) := certificate_66_part_7_E

noncomputable def certificate_66_part_12_E : List (ℕ × ℕ) := certificate_66_part_9_E

noncomputable def certificate_67_q : Finset ℕ := ([0,1,2,4,6] : List ℕ).toFinset
noncomputable def certificate_67_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,4),(0,6),(1,2),(1,4),(1,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_68_q : Finset ℕ := ([0,1,2,4,7] : List ℕ).toFinset
noncomputable def certificate_68_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,4),(0,7),(1,2),(1,4),(1,7),(2,4),(2,7),(4,7)]

noncomputable def certificate_69_q : Finset ℕ := ([0,1,3,4,6] : List ℕ).toFinset
noncomputable def certificate_69_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(0,1),(0,3),(0,4),(0,6),(1,3),(1,4),(1,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_70_q : Finset ℕ := ([0,1,3,4,7] : List ℕ).toFinset
noncomputable def certificate_70_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(0,1),(0,3),(0,4),(0,7),(1,3),(1,4),(1,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_71_q : Finset ℕ := ([0,1,3,5,7] : List ℕ).toFinset
noncomputable def certificate_71_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,3),(0,5),(0,7),(1,3),(1,5),(1,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_72_q : Finset ℕ := ([0,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_72_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(0,2),(0,3),(0,5),(0,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_73_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_73_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_74_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_74_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_75_q : Finset ℕ := ([0,1,2,3,4,7] : List ℕ).toFinset
noncomputable def certificate_75_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,3),(1,4),(1,7),(2,3),(2,4),(2,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_76_q : Finset ℕ := ([0,1,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_76_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,5),(0,7),(1,2),(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_77_q : Finset ℕ := ([0,1,2,4,5,7] : List ℕ).toFinset
noncomputable def certificate_77_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(0,1),(0,2),(0,4),(0,5),(0,7),(1,2),(1,4),(1,5),(1,7),(2,4),(2,5),(2,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_78_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_78_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_79_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_79_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_80_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_80_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

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

noncomputable def certificate_306_q : Finset ℕ := ([0,1,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_306_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,10),(1,3),(1,4),(1,6),(1,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_307_q : Finset ℕ := ([0,1,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_307_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,7),(0,10),(1,3),(1,4),(1,7),(1,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_308_q : Finset ℕ := ([0,1,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_308_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,6),(0,9),(1,3),(1,5),(1,6),(1,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_309_q : Finset ℕ := ([0,1,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_309_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,10),(1,3),(1,5),(1,6),(1,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_310_q : Finset ℕ := ([0,1,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_310_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,7),(0,9),(1,3),(1,5),(1,7),(1,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_311_q : Finset ℕ := ([0,1,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_311_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,7),(0,10),(1,3),(1,5),(1,7),(1,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_312_q : Finset ℕ := ([0,1,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_312_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,8),(0,10),(1,3),(1,5),(1,8),(1,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_313_q : Finset ℕ := ([0,1,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_313_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,6),(0,7),(0,10),(1,3),(1,6),(1,7),(1,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_314_q : Finset ℕ := ([0,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_314_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(0,2),(0,3),(0,5),(0,6),(0,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_315_q : Finset ℕ := ([0,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_315_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,6),(0,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_316_q : Finset ℕ := ([0,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_316_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_317_q : Finset ℕ := ([0,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_317_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,7),(0,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_318_q : Finset ℕ := ([0,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_318_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,7),(0,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_319_q : Finset ℕ := ([0,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_319_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,8),(0,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_320_q : Finset ℕ := ([0,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_320_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,3),(0,6),(0,7),(0,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_321_q : Finset ℕ := ([0,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_321_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,5),(0,7),(0,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_322_q : Finset ℕ := ([0,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_322_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,5),(0,7),(0,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_323_q : Finset ℕ := ([0,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_323_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,7),(0,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_324_q : Finset ℕ := ([0,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_324_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,8),(0,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_325_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_325_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_326_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_326_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_327_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_327_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_328_q : Finset ℕ := ([0,1,2,3,4,5,9] : List ℕ).toFinset
noncomputable def certificate_328_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(1,2),(1,3),(1,4),(1,5),(1,9),(2,3),(2,4),(2,5),(2,9),(3,4),(3,5),(3,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_329_q : Finset ℕ := ([0,1,2,3,4,5,10] : List ℕ).toFinset
noncomputable def certificate_329_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(1,2),(1,3),(1,4),(1,5),(1,10),(2,3),(2,4),(2,5),(2,10),(3,4),(3,5),(3,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_330_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_330_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_331_q : Finset ℕ := ([0,1,2,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_331_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(1,2),(1,3),(1,4),(1,6),(1,9),(2,3),(2,4),(2,6),(2,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_332_q : Finset ℕ := ([0,1,2,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_332_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(1,2),(1,3),(1,4),(1,6),(1,10),(2,3),(2,4),(2,6),(2,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_333_q : Finset ℕ := ([0,1,2,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_333_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(1,2),(1,3),(1,4),(1,7),(1,10),(2,3),(2,4),(2,7),(2,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_334_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_334_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_335_q : Finset ℕ := ([0,1,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_335_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(1,2),(1,3),(1,5),(1,6),(1,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_336_q : Finset ℕ := ([0,1,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_336_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(1,2),(1,3),(1,5),(1,6),(1,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_337_q : Finset ℕ := ([0,1,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_337_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(1,2),(1,3),(1,5),(1,7),(1,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_338_q : Finset ℕ := ([0,1,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_338_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(1,2),(1,3),(1,5),(1,7),(1,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_339_q : Finset ℕ := ([0,1,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_339_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(1,2),(1,3),(1,5),(1,8),(1,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_340_q : Finset ℕ := ([0,1,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_340_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(1,2),(1,3),(1,6),(1,7),(1,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_341_q : Finset ℕ := ([0,1,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_341_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(1,2),(1,4),(1,5),(1,7),(1,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_342_q : Finset ℕ := ([0,1,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_342_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(1,2),(1,4),(1,5),(1,7),(1,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_343_q : Finset ℕ := ([0,1,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_343_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(1,2),(1,4),(1,6),(1,7),(1,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_344_q : Finset ℕ := ([0,1,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_344_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(1,2),(1,4),(1,6),(1,8),(1,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_345_q : Finset ℕ := ([0,1,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_345_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(1,3),(1,4),(1,6),(1,7),(1,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_346_q : Finset ℕ := ([0,1,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_346_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(1,3),(1,4),(1,6),(1,7),(1,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_347_q : Finset ℕ := ([0,1,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_347_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(1,3),(1,4),(1,6),(1,8),(1,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_348_q : Finset ℕ := ([0,1,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_348_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(1,3),(1,5),(1,6),(1,8),(1,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_349_q : Finset ℕ := ([0,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_349_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_350_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_350_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_351_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_351_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

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

noncomputable def certificate_352_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_352_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_353_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_353_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_354_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_354_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_355_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_355_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_356_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_356_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_357_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_357_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_358_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_358_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_359_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_359_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_360_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset
noncomputable def certificate_360_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_361_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_361_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_362_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_362_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_363_q : Finset ℕ := ([0,1,2,3,4,7] : List ℕ).toFinset
noncomputable def certificate_363_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,3),(1,4),(1,7),(2,3),(2,4),(2,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_364_q : Finset ℕ := ([0,1,2,3,4,8] : List ℕ).toFinset
noncomputable def certificate_364_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,8),(1,2),(1,3),(1,4),(1,8),(2,3),(2,4),(2,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_365_q : Finset ℕ := ([0,1,2,3,4,9] : List ℕ).toFinset
noncomputable def certificate_365_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,9),(1,2),(1,3),(1,4),(1,9),(2,3),(2,4),(2,9),(3,4),(3,9),(4,9)]

noncomputable def certificate_366_q : Finset ℕ := ([0,1,2,3,4,10] : List ℕ).toFinset
noncomputable def certificate_366_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,10),(1,2),(1,3),(1,4),(1,10),(2,3),(2,4),(2,10),(3,4),(3,10),(4,10)]

noncomputable def certificate_367_q : Finset ℕ := ([0,1,2,3,4,11] : List ℕ).toFinset

noncomputable def certificate_367_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,11),(1,2),(1,3),(1,4),(1,11),(2,3),(2,4),(2,11),(3,4),(3,11),(4,11)]

noncomputable def certificate_367_E : List (ℕ × ℕ) := certificate_367_edges

noncomputable def certificate_367_part_1_E : List (ℕ × ℕ) := certificate_367_E

noncomputable def certificate_367_part_2_E : List (ℕ × ℕ) := certificate_367_part_1_E

noncomputable def certificate_367_part_3_E : List (ℕ × ℕ) := certificate_367_part_2_E

noncomputable def certificate_367_part_4_E : List (ℕ × ℕ) := certificate_367_part_3_E

noncomputable def certificate_367_part_5_E : List (ℕ × ℕ) := certificate_367_part_4_E

noncomputable def certificate_367_part_6_E : List (ℕ × ℕ) := certificate_367_part_5_E

noncomputable def certificate_367_part_7_E : List (ℕ × ℕ) := certificate_367_part_6_E

noncomputable def certificate_367_part_8_E : List (ℕ × ℕ) := certificate_367_part_7_E

noncomputable def certificate_367_part_10_E : List (ℕ × ℕ) := certificate_367_part_8_E

noncomputable def certificate_367_part_18_E : List (ℕ × ℕ) := certificate_367_part_10_E

noncomputable def certificate_367_part_35_E : List (ℕ × ℕ) := certificate_367_part_18_E

noncomputable def certificate_367_part_54_E : List (ℕ × ℕ) := certificate_367_part_35_E

noncomputable def certificate_367_part_73_E : List (ℕ × ℕ) := certificate_367_part_54_E

noncomputable def certificate_367_part_74_E : List (ℕ × ℕ) := certificate_367_part_73_E

noncomputable def certificate_367_part_75_E : List (ℕ × ℕ) := certificate_367_part_74_E

noncomputable def certificate_367_part_76_E : List (ℕ × ℕ) := certificate_367_part_75_E

noncomputable def certificate_367_part_77_E : List (ℕ × ℕ) := certificate_367_part_76_E

noncomputable def certificate_367_part_78_E : List (ℕ × ℕ) := certificate_367_part_77_E

noncomputable def certificate_368_q : Finset ℕ := ([0,1,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_368_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,5),(0,7),(1,2),(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_369_q : Finset ℕ := ([0,1,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_369_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,8),(1,2),(1,3),(1,5),(1,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_370_q : Finset ℕ := ([0,1,2,3,5,9] : List ℕ).toFinset
noncomputable def certificate_370_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,9),(1,2),(1,3),(1,5),(1,9),(2,3),(2,5),(2,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_371_q : Finset ℕ := ([0,1,2,3,5,10] : List ℕ).toFinset
noncomputable def certificate_371_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,10),(1,2),(1,3),(1,5),(1,10),(2,3),(2,5),(2,10),(3,5),(3,10),(5,10)]

noncomputable def certificate_372_q : Finset ℕ := ([0,1,2,3,5,11] : List ℕ).toFinset
noncomputable def certificate_372_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,11),(1,2),(1,3),(1,5),(1,11),(2,3),(2,5),(2,11),(3,5),(3,11),(5,11)]

noncomputable def certificate_373_q : Finset ℕ := ([0,1,2,3,6,9] : List ℕ).toFinset
noncomputable def certificate_373_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,6),(0,9),(1,2),(1,3),(1,6),(1,9),(2,3),(2,6),(2,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_374_q : Finset ℕ := ([0,1,2,3,6,10] : List ℕ).toFinset
noncomputable def certificate_374_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,10),(1,2),(1,3),(1,6),(1,10),(2,3),(2,6),(2,10),(3,6),(3,10),(6,10)]

noncomputable def certificate_375_q : Finset ℕ := ([0,1,2,3,6,11] : List ℕ).toFinset
noncomputable def certificate_375_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,11),(1,2),(1,3),(1,6),(1,11),(2,3),(2,6),(2,11),(3,6),(3,11),(6,11)]

noncomputable def certificate_376_q : Finset ℕ := ([0,1,2,3,7,11] : List ℕ).toFinset

noncomputable def certificate_376_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,7),(0,11),(1,2),(1,3),(1,7),(1,11),(2,3),(2,7),(2,11),(3,7),(3,11),(7,11)]

noncomputable def certificate_376_E : List (ℕ × ℕ) := certificate_376_edges

noncomputable def certificate_376_part_1_E : List (ℕ × ℕ) := certificate_376_E

noncomputable def certificate_376_part_2_E : List (ℕ × ℕ) := certificate_376_part_1_E

noncomputable def certificate_376_part_3_E : List (ℕ × ℕ) := certificate_376_part_2_E

noncomputable def certificate_376_part_4_E : List (ℕ × ℕ) := certificate_376_part_3_E

noncomputable def certificate_376_part_5_E : List (ℕ × ℕ) := certificate_376_part_4_E

noncomputable def certificate_376_part_6_E : List (ℕ × ℕ) := certificate_376_part_5_E

noncomputable def certificate_376_part_7_E : List (ℕ × ℕ) := certificate_376_part_6_E

noncomputable def certificate_376_part_9_E : List (ℕ × ℕ) := certificate_376_part_7_E

noncomputable def certificate_376_part_11_E : List (ℕ × ℕ) := certificate_376_part_9_E

noncomputable def certificate_376_part_12_E : List (ℕ × ℕ) := certificate_376_part_11_E

noncomputable def certificate_376_part_17_E : List (ℕ × ℕ) := certificate_376_part_12_E

noncomputable def certificate_376_part_22_E : List (ℕ × ℕ) := certificate_376_part_17_E

noncomputable def certificate_376_part_24_E : List (ℕ × ℕ) := certificate_376_part_22_E

noncomputable def certificate_376_part_26_E : List (ℕ × ℕ) := certificate_376_part_24_E

noncomputable def certificate_376_part_27_E : List (ℕ × ℕ) := certificate_376_part_26_E

noncomputable def certificate_376_part_31_E : List (ℕ × ℕ) := certificate_376_part_27_E

noncomputable def certificate_376_part_34_E : List (ℕ × ℕ) := certificate_376_part_31_E

noncomputable def certificate_377_q : Finset ℕ := ([0,1,2,4,5,7] : List ℕ).toFinset
noncomputable def certificate_377_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(0,1),(0,2),(0,4),(0,5),(0,7),(1,2),(1,4),(1,5),(1,7),(2,4),(2,5),(2,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_378_q : Finset ℕ := ([0,1,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_378_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,5),(0,8),(1,2),(1,4),(1,5),(1,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_379_q : Finset ℕ := ([0,1,2,4,5,9] : List ℕ).toFinset
noncomputable def certificate_379_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,9),(1,2),(1,4),(1,5),(1,9),(2,4),(2,5),(2,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_380_q : Finset ℕ := ([0,1,2,4,5,10] : List ℕ).toFinset
noncomputable def certificate_380_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,10),(1,2),(1,4),(1,5),(1,10),(2,4),(2,5),(2,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_381_q : Finset ℕ := ([0,1,2,4,5,11] : List ℕ).toFinset
noncomputable def certificate_381_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,11),(1,2),(1,4),(1,5),(1,11),(2,4),(2,5),(2,11),(4,5),(4,11),(5,11)]

noncomputable def certificate_382_q : Finset ℕ := ([0,1,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_382_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,6),(0,8),(1,2),(1,4),(1,6),(1,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_383_q : Finset ℕ := ([0,1,2,4,6,9] : List ℕ).toFinset
noncomputable def certificate_383_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,6),(0,9),(1,2),(1,4),(1,6),(1,9),(2,4),(2,6),(2,9),(4,6),(4,9),(6,9)]

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

noncomputable def certificate_384_q : Finset ℕ := ([0,1,2,4,6,10] : List ℕ).toFinset
noncomputable def certificate_384_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,10),(1,2),(1,4),(1,6),(1,10),(2,4),(2,6),(2,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_385_q : Finset ℕ := ([0,1,2,4,6,11] : List ℕ).toFinset
noncomputable def certificate_385_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,11),(1,2),(1,4),(1,6),(1,11),(2,4),(2,6),(2,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_386_q : Finset ℕ := ([0,1,2,4,7,9] : List ℕ).toFinset
noncomputable def certificate_386_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,7),(0,9),(1,2),(1,4),(1,7),(1,9),(2,4),(2,7),(2,9),(4,7),(4,9),(7,9)]

noncomputable def certificate_387_q : Finset ℕ := ([0,1,2,4,7,10] : List ℕ).toFinset
noncomputable def certificate_387_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,7),(0,10),(1,2),(1,4),(1,7),(1,10),(2,4),(2,7),(2,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_388_q : Finset ℕ := ([0,1,2,4,7,11] : List ℕ).toFinset
noncomputable def certificate_388_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,7),(0,11),(1,2),(1,4),(1,7),(1,11),(2,4),(2,7),(2,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_389_q : Finset ℕ := ([0,1,2,4,8,10] : List ℕ).toFinset
noncomputable def certificate_389_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,8),(0,10),(1,2),(1,4),(1,8),(1,10),(2,4),(2,8),(2,10),(4,8),(4,10),(8,10)]

noncomputable def certificate_390_q : Finset ℕ := ([0,1,2,4,8,11] : List ℕ).toFinset
noncomputable def certificate_390_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,8),(0,11),(1,2),(1,4),(1,8),(1,11),(2,4),(2,8),(2,11),(4,8),(4,11),(8,11)]

noncomputable def certificate_391_q : Finset ℕ := ([0,1,2,4,9,11] : List ℕ).toFinset
noncomputable def certificate_391_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,9),(0,11),(1,2),(1,4),(1,9),(1,11),(2,4),(2,9),(2,11),(4,9),(4,11),(9,11)]

noncomputable def certificate_392_q : Finset ℕ := ([0,1,2,5,6,9] : List ℕ).toFinset
noncomputable def certificate_392_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,5),(0,6),(0,9),(1,2),(1,5),(1,6),(1,9),(2,5),(2,6),(2,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_393_q : Finset ℕ := ([0,1,2,5,6,10] : List ℕ).toFinset
noncomputable def certificate_393_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,6),(0,10),(1,2),(1,5),(1,6),(1,10),(2,5),(2,6),(2,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_394_q : Finset ℕ := ([0,1,2,5,6,11] : List ℕ).toFinset
noncomputable def certificate_394_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,5),(0,6),(0,11),(1,2),(1,5),(1,6),(1,11),(2,5),(2,6),(2,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_395_q : Finset ℕ := ([0,1,2,5,7,10] : List ℕ).toFinset
noncomputable def certificate_395_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,7),(0,10),(1,2),(1,5),(1,7),(1,10),(2,5),(2,7),(2,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_396_q : Finset ℕ := ([0,1,2,5,7,11] : List ℕ).toFinset
noncomputable def certificate_396_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,5),(0,7),(0,11),(1,2),(1,5),(1,7),(1,11),(2,5),(2,7),(2,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_397_q : Finset ℕ := ([0,1,2,5,8,11] : List ℕ).toFinset
noncomputable def certificate_397_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,5),(0,8),(0,11),(1,2),(1,5),(1,8),(1,11),(2,5),(2,8),(2,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_398_q : Finset ℕ := ([0,1,2,6,7,11] : List ℕ).toFinset

noncomputable def certificate_398_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,6),(0,7),(0,11),(1,2),(1,6),(1,7),(1,11),(2,6),(2,7),(2,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_398_E : List (ℕ × ℕ) := certificate_398_edges

noncomputable def certificate_398_part_1_E : List (ℕ × ℕ) := certificate_398_E

noncomputable def certificate_398_part_2_E : List (ℕ × ℕ) := certificate_398_part_1_E

noncomputable def certificate_398_part_3_E : List (ℕ × ℕ) := certificate_398_part_2_E

noncomputable def certificate_398_part_4_E : List (ℕ × ℕ) := certificate_398_part_3_E

noncomputable def certificate_398_part_5_E : List (ℕ × ℕ) := certificate_398_part_4_E

noncomputable def certificate_398_part_6_E : List (ℕ × ℕ) := certificate_398_part_5_E

noncomputable def certificate_398_part_7_E : List (ℕ × ℕ) := certificate_398_part_6_E

noncomputable def certificate_398_part_9_E : List (ℕ × ℕ) := certificate_398_part_7_E

noncomputable def certificate_398_part_10_E : List (ℕ × ℕ) := certificate_398_part_9_E

noncomputable def certificate_398_part_11_E : List (ℕ × ℕ) := certificate_398_part_10_E

noncomputable def certificate_398_part_12_E : List (ℕ × ℕ) := certificate_398_part_11_E

noncomputable def certificate_398_part_13_E : List (ℕ × ℕ) := certificate_398_part_12_E

noncomputable def certificate_398_part_15_E : List (ℕ × ℕ) := certificate_398_part_13_E

noncomputable def certificate_398_part_16_E : List (ℕ × ℕ) := certificate_398_part_15_E

noncomputable def certificate_398_part_17_E : List (ℕ × ℕ) := certificate_398_part_16_E

noncomputable def certificate_398_part_18_E : List (ℕ × ℕ) := certificate_398_part_17_E

noncomputable def certificate_398_part_22_E : List (ℕ × ℕ) := certificate_398_part_18_E

noncomputable def certificate_398_part_23_E : List (ℕ × ℕ) := certificate_398_part_22_E

noncomputable def certificate_398_part_29_E : List (ℕ × ℕ) := certificate_398_part_23_E

noncomputable def certificate_398_part_30_E : List (ℕ × ℕ) := certificate_398_part_29_E

noncomputable def certificate_398_part_35_E : List (ℕ × ℕ) := certificate_398_part_30_E

noncomputable def certificate_398_part_40_E : List (ℕ × ℕ) := certificate_398_part_35_E

noncomputable def certificate_398_part_41_E : List (ℕ × ℕ) := certificate_398_part_40_E

noncomputable def certificate_399_q : Finset ℕ := ([0,1,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_399_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,6),(0,8),(1,3),(1,4),(1,6),(1,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_400_q : Finset ℕ := ([0,1,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_400_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,9),(1,3),(1,4),(1,6),(1,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_401_q : Finset ℕ := ([0,1,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_401_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,10),(1,3),(1,4),(1,6),(1,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_402_q : Finset ℕ := ([0,1,3,4,6,11] : List ℕ).toFinset
noncomputable def certificate_402_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,11),(1,3),(1,4),(1,6),(1,11),(3,4),(3,6),(3,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_403_q : Finset ℕ := ([0,1,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_403_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,7),(0,10),(1,3),(1,4),(1,7),(1,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_404_q : Finset ℕ := ([0,1,3,4,7,11] : List ℕ).toFinset
noncomputable def certificate_404_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,7),(0,11),(1,3),(1,4),(1,7),(1,11),(3,4),(3,7),(3,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_405_q : Finset ℕ := ([0,1,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_405_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,6),(0,9),(1,3),(1,5),(1,6),(1,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_406_q : Finset ℕ := ([0,1,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_406_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,10),(1,3),(1,5),(1,6),(1,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_407_q : Finset ℕ := ([0,1,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_407_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,6),(0,11),(1,3),(1,5),(1,6),(1,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_408_q : Finset ℕ := ([0,1,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_408_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,7),(0,9),(1,3),(1,5),(1,7),(1,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_409_q : Finset ℕ := ([0,1,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_409_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,7),(0,10),(1,3),(1,5),(1,7),(1,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_410_q : Finset ℕ := ([0,1,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_410_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,11),(1,3),(1,5),(1,7),(1,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_411_q : Finset ℕ := ([0,1,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_411_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,8),(0,10),(1,3),(1,5),(1,8),(1,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_412_q : Finset ℕ := ([0,1,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_412_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,8),(0,11),(1,3),(1,5),(1,8),(1,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_413_q : Finset ℕ := ([0,1,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_413_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,9),(0,11),(1,3),(1,5),(1,9),(1,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_414_q : Finset ℕ := ([0,1,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_414_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,6),(0,7),(0,10),(1,3),(1,6),(1,7),(1,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_415_q : Finset ℕ := ([0,1,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_415_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,6),(0,7),(0,11),(1,3),(1,6),(1,7),(1,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_416_q : Finset ℕ := ([0,1,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_416_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,6),(0,8),(0,11),(1,3),(1,6),(1,8),(1,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_417_q : Finset ℕ := ([0,1,3,6,9,11] : List ℕ).toFinset
noncomputable def certificate_417_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,6),(0,9),(0,11),(1,3),(1,6),(1,9),(1,11),(3,6),(3,9),(3,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_418_q : Finset ℕ := ([0,1,3,7,8,11] : List ℕ).toFinset
noncomputable def certificate_418_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,7),(0,8),(0,11),(1,3),(1,7),(1,8),(1,11),(3,7),(3,8),(3,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_419_q : Finset ℕ := ([0,1,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_419_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,4),(0,5),(0,8),(0,11),(1,4),(1,5),(1,8),(1,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_420_q : Finset ℕ := ([0,1,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_420_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,4),(0,6),(0,8),(0,11),(1,4),(1,6),(1,8),(1,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_421_q : Finset ℕ := ([0,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_421_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(0,2),(0,3),(0,5),(0,6),(0,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_422_q : Finset ℕ := ([0,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_422_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,6),(0,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_423_q : Finset ℕ := ([0,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_423_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_424_q : Finset ℕ := ([0,2,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_424_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,11),(2,3),(2,5),(2,6),(2,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_425_q : Finset ℕ := ([0,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_425_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,7),(0,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_426_q : Finset ℕ := ([0,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_426_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,7),(0,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_427_q : Finset ℕ := ([0,2,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_427_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,11),(2,3),(2,5),(2,7),(2,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_428_q : Finset ℕ := ([0,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_428_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,8),(0,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_429_q : Finset ℕ := ([0,2,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_429_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,8),(0,11),(2,3),(2,5),(2,8),(2,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_430_q : Finset ℕ := ([0,2,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_430_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,9),(0,11),(2,3),(2,5),(2,9),(2,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_431_q : Finset ℕ := ([0,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_431_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,3),(0,6),(0,7),(0,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_432_q : Finset ℕ := ([0,2,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_432_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,6),(0,7),(0,11),(2,3),(2,6),(2,7),(2,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_433_q : Finset ℕ := ([0,2,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_433_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,6),(0,8),(0,11),(2,3),(2,6),(2,8),(2,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_434_q : Finset ℕ := ([0,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_434_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,5),(0,7),(0,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_435_q : Finset ℕ := ([0,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_435_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,5),(0,7),(0,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_436_q : Finset ℕ := ([0,2,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_436_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,7),(0,11),(2,4),(2,5),(2,7),(2,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_437_q : Finset ℕ := ([0,2,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_437_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,8),(0,11),(2,4),(2,5),(2,8),(2,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_438_q : Finset ℕ := ([0,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_438_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,7),(0,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_439_q : Finset ℕ := ([0,2,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_439_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,6),(0,7),(0,11),(2,4),(2,6),(2,7),(2,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_440_q : Finset ℕ := ([0,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_440_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,8),(0,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_441_q : Finset ℕ := ([0,2,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_441_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,6),(0,8),(0,11),(2,4),(2,6),(2,8),(2,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_442_q : Finset ℕ := ([0,2,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_442_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,6),(0,9),(0,11),(2,4),(2,6),(2,9),(2,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_443_q : Finset ℕ := ([0,2,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_443_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,4),(0,7),(0,8),(0,11),(2,4),(2,7),(2,8),(2,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_444_q : Finset ℕ := ([0,2,4,7,9,11] : List ℕ).toFinset
noncomputable def certificate_444_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,7),(0,9),(0,11),(2,4),(2,7),(2,9),(2,11),(4,7),(4,9),(4,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_445_q : Finset ℕ := ([0,2,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_445_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,5),(0,6),(0,8),(0,11),(2,5),(2,6),(2,8),(2,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_446_q : Finset ℕ := ([0,2,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_446_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,5),(0,7),(0,8),(0,11),(2,5),(2,7),(2,8),(2,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_447_q : Finset ℕ := ([0,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_447_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,3),(0,4),(0,7),(0,8),(0,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_448_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_448_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_449_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_449_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_450_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_450_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_451_q : Finset ℕ := ([0,1,2,3,4,5,9] : List ℕ).toFinset
noncomputable def certificate_451_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(1,2),(1,3),(1,4),(1,5),(1,9),(2,3),(2,4),(2,5),(2,9),(3,4),(3,5),(3,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_452_q : Finset ℕ := ([0,1,2,3,4,5,10] : List ℕ).toFinset
noncomputable def certificate_452_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(1,2),(1,3),(1,4),(1,5),(1,10),(2,3),(2,4),(2,5),(2,10),(3,4),(3,5),(3,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_453_q : Finset ℕ := ([0,1,2,3,4,5,11] : List ℕ).toFinset
noncomputable def certificate_453_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,11),(1,2),(1,3),(1,4),(1,5),(1,11),(2,3),(2,4),(2,5),(2,11),(3,4),(3,5),(3,11),(4,5),(4,11),(5,11)]

noncomputable def certificate_454_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_454_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_455_q : Finset ℕ := ([0,1,2,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_455_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(1,2),(1,3),(1,4),(1,6),(1,9),(2,3),(2,4),(2,6),(2,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_456_q : Finset ℕ := ([0,1,2,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_456_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(1,2),(1,3),(1,4),(1,6),(1,10),(2,3),(2,4),(2,6),(2,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_457_q : Finset ℕ := ([0,1,2,3,4,6,11] : List ℕ).toFinset
noncomputable def certificate_457_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(1,2),(1,3),(1,4),(1,6),(1,11),(2,3),(2,4),(2,6),(2,11),(3,4),(3,6),(3,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_458_q : Finset ℕ := ([0,1,2,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_458_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(1,2),(1,3),(1,4),(1,7),(1,10),(2,3),(2,4),(2,7),(2,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_459_q : Finset ℕ := ([0,1,2,3,4,7,11] : List ℕ).toFinset
noncomputable def certificate_459_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(1,2),(1,3),(1,4),(1,7),(1,11),(2,3),(2,4),(2,7),(2,11),(3,4),(3,7),(3,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_460_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_460_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_461_q : Finset ℕ := ([0,1,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_461_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(1,2),(1,3),(1,5),(1,6),(1,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_462_q : Finset ℕ := ([0,1,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_462_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(1,2),(1,3),(1,5),(1,6),(1,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_463_q : Finset ℕ := ([0,1,2,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_463_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,11),(1,2),(1,3),(1,5),(1,6),(1,11),(2,3),(2,5),(2,6),(2,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_464_q : Finset ℕ := ([0,1,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_464_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(1,2),(1,3),(1,5),(1,7),(1,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_465_q : Finset ℕ := ([0,1,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_465_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(1,2),(1,3),(1,5),(1,7),(1,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_466_q : Finset ℕ := ([0,1,2,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_466_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(1,2),(1,3),(1,5),(1,7),(1,11),(2,3),(2,5),(2,7),(2,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_467_q : Finset ℕ := ([0,1,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_467_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(1,2),(1,3),(1,5),(1,8),(1,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_468_q : Finset ℕ := ([0,1,2,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_468_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(1,2),(1,3),(1,5),(1,8),(1,11),(2,3),(2,5),(2,8),(2,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_469_q : Finset ℕ := ([0,1,2,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_469_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(1,2),(1,3),(1,5),(1,9),(1,11),(2,3),(2,5),(2,9),(2,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_470_q : Finset ℕ := ([0,1,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_470_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(1,2),(1,3),(1,6),(1,7),(1,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_471_q : Finset ℕ := ([0,1,2,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_471_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(1,2),(1,3),(1,6),(1,7),(1,11),(2,3),(2,6),(2,7),(2,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_472_q : Finset ℕ := ([0,1,2,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_472_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(1,2),(1,3),(1,6),(1,8),(1,11),(2,3),(2,6),(2,8),(2,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_473_q : Finset ℕ := ([0,1,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_473_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(1,2),(1,4),(1,5),(1,7),(1,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_474_q : Finset ℕ := ([0,1,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_474_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(1,2),(1,4),(1,5),(1,7),(1,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_475_q : Finset ℕ := ([0,1,2,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_475_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(1,2),(1,4),(1,5),(1,7),(1,11),(2,4),(2,5),(2,7),(2,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_476_q : Finset ℕ := ([0,1,2,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_476_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(1,2),(1,4),(1,5),(1,8),(1,11),(2,4),(2,5),(2,8),(2,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_477_q : Finset ℕ := ([0,1,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_477_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(1,2),(1,4),(1,6),(1,7),(1,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_478_q : Finset ℕ := ([0,1,2,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_478_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(1,2),(1,4),(1,6),(1,7),(1,11),(2,4),(2,6),(2,7),(2,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_479_q : Finset ℕ := ([0,1,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_479_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(1,2),(1,4),(1,6),(1,8),(1,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

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

noncomputable def certificate_480_q : Finset ℕ := ([0,1,2,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_480_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(1,2),(1,4),(1,6),(1,8),(1,11),(2,4),(2,6),(2,8),(2,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_481_q : Finset ℕ := ([0,1,2,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_481_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(1,2),(1,4),(1,6),(1,9),(1,11),(2,4),(2,6),(2,9),(2,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_482_q : Finset ℕ := ([0,1,2,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_482_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(1,2),(1,4),(1,7),(1,8),(1,11),(2,4),(2,7),(2,8),(2,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_483_q : Finset ℕ := ([0,1,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_483_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(1,3),(1,4),(1,6),(1,7),(1,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_484_q : Finset ℕ := ([0,1,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_484_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(1,3),(1,4),(1,6),(1,7),(1,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_485_q : Finset ℕ := ([0,1,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_485_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(1,3),(1,4),(1,6),(1,7),(1,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_486_q : Finset ℕ := ([0,1,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_486_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(1,3),(1,4),(1,6),(1,8),(1,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_487_q : Finset ℕ := ([0,1,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_487_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(1,3),(1,4),(1,6),(1,8),(1,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_488_q : Finset ℕ := ([0,1,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_488_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(1,3),(1,4),(1,6),(1,9),(1,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_489_q : Finset ℕ := ([0,1,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_489_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(1,3),(1,4),(1,7),(1,8),(1,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_490_q : Finset ℕ := ([0,1,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_490_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(1,3),(1,5),(1,6),(1,8),(1,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_491_q : Finset ℕ := ([0,1,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_491_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(1,3),(1,5),(1,6),(1,8),(1,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_492_q : Finset ℕ := ([0,1,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_492_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(1,3),(1,5),(1,7),(1,8),(1,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_493_q : Finset ℕ := ([0,1,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_493_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(1,3),(1,5),(1,7),(1,9),(1,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_494_q : Finset ℕ := ([0,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_494_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_495_q : Finset ℕ := ([0,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_495_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_496_q : Finset ℕ := ([0,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_496_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_497_q : Finset ℕ := ([0,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_497_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_498_q : Finset ℕ := ([0,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_498_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_499_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_499_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_500_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_500_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_501_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_501_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_502_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_502_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_503_q : Finset ℕ := ([0,1,2,3,4,5,6,11] : List ℕ).toFinset
noncomputable def certificate_503_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,11),(1,2),(1,3),(1,4),(1,5),(1,6),(1,11),(2,3),(2,4),(2,5),(2,6),(2,11),(3,4),(3,5),(3,6),(3,11),(4,5),(4,6),(4,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_504_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_504_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_505_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_505_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_506_q : Finset ℕ := ([0,1,2,3,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_506_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,11),(1,2),(1,3),(1,4),(1,5),(1,7),(1,11),(2,3),(2,4),(2,5),(2,7),(2,11),(3,4),(3,5),(3,7),(3,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_507_q : Finset ℕ := ([0,1,2,3,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_507_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,11),(1,2),(1,3),(1,4),(1,5),(1,8),(1,11),(2,3),(2,4),(2,5),(2,8),(2,11),(3,4),(3,5),(3,8),(3,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_508_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_508_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_509_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_509_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_510_q : Finset ℕ := ([0,1,2,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_510_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,11),(1,2),(1,3),(1,4),(1,6),(1,7),(1,11),(2,3),(2,4),(2,6),(2,7),(2,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_511_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_511_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

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

noncomputable def certificate_512_q : Finset ℕ := ([0,1,2,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_512_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,11),(1,2),(1,3),(1,4),(1,6),(1,8),(1,11),(2,3),(2,4),(2,6),(2,8),(2,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_513_q : Finset ℕ := ([0,1,2,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_513_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,11),(1,2),(1,3),(1,4),(1,6),(1,9),(1,11),(2,3),(2,4),(2,6),(2,9),(2,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_514_q : Finset ℕ := ([0,1,2,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_514_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,11),(1,2),(1,3),(1,4),(1,7),(1,8),(1,11),(2,3),(2,4),(2,7),(2,8),(2,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_515_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_515_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_516_q : Finset ℕ := ([0,1,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_516_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(1,2),(1,3),(1,5),(1,6),(1,8),(1,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_517_q : Finset ℕ := ([0,1,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_517_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(1,2),(1,3),(1,5),(1,7),(1,8),(1,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_518_q : Finset ℕ := ([0,1,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_518_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(1,2),(1,3),(1,5),(1,7),(1,9),(1,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_519_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset
noncomputable def certificate_519_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_520_q : Finset ℕ := ([0,1,2,4,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_520_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,11),(1,2),(1,4),(1,5),(1,7),(1,8),(1,11),(2,4),(2,5),(2,7),(2,8),(2,11),(4,5),(4,7),(4,8),(4,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_521_q : Finset ℕ := ([0,1,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_521_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(1,2),(1,4),(1,5),(1,7),(1,9),(1,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_522_q : Finset ℕ := ([0,1,2,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_522_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(1,2),(1,4),(1,6),(1,7),(1,9),(1,11),(2,4),(2,6),(2,7),(2,9),(2,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_523_q : Finset ℕ := ([0,1,3,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_523_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,11),(1,3),(1,4),(1,6),(1,7),(1,9),(1,11),(3,4),(3,6),(3,7),(3,9),(3,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_524_q : Finset ℕ := ([0,2,3,5,6,8,9,11] : List ℕ).toFinset
noncomputable def certificate_524_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,11),(2,3),(2,5),(2,6),(2,8),(2,9),(2,11),(3,5),(3,6),(3,8),(3,9),(3,11),(5,6),(5,8),(5,9),(5,11),(6,8),(6,9),(6,11),(8,9),(8,11),(9,11)]

noncomputable def certificate_525_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_525_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_526_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_526_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_527_q : Finset ℕ := ([0,1,2,3,4,7] : List ℕ).toFinset
noncomputable def certificate_527_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,3),(1,4),(1,7),(2,3),(2,4),(2,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_528_q : Finset ℕ := ([0,1,2,3,4,8] : List ℕ).toFinset
noncomputable def certificate_528_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,8),(1,2),(1,3),(1,4),(1,8),(2,3),(2,4),(2,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_529_q : Finset ℕ := ([0,1,2,3,4,9] : List ℕ).toFinset
noncomputable def certificate_529_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,9),(1,2),(1,3),(1,4),(1,9),(2,3),(2,4),(2,9),(3,4),(3,9),(4,9)]

noncomputable def certificate_530_q : Finset ℕ := ([0,1,2,3,4,10] : List ℕ).toFinset
noncomputable def certificate_530_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,10),(1,2),(1,3),(1,4),(1,10),(2,3),(2,4),(2,10),(3,4),(3,10),(4,10)]

noncomputable def certificate_531_q : Finset ℕ := ([0,1,2,3,4,11] : List ℕ).toFinset
noncomputable def certificate_531_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,11),(1,2),(1,3),(1,4),(1,11),(2,3),(2,4),(2,11),(3,4),(3,11),(4,11)]

noncomputable def certificate_532_q : Finset ℕ := ([0,1,2,3,4,12] : List ℕ).toFinset

noncomputable def certificate_532_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,12),(1,2),(1,3),(1,4),(1,12),(2,3),(2,4),(2,12),(3,4),(3,12),(4,12)]

noncomputable def certificate_532_E : List (ℕ × ℕ) := certificate_532_edges

noncomputable def certificate_532_part_1_E : List (ℕ × ℕ) := certificate_532_E

noncomputable def certificate_532_part_2_E : List (ℕ × ℕ) := certificate_532_part_1_E

noncomputable def certificate_532_part_3_E : List (ℕ × ℕ) := certificate_532_part_2_E

noncomputable def certificate_532_part_4_E : List (ℕ × ℕ) := certificate_532_part_3_E

noncomputable def certificate_532_part_5_E : List (ℕ × ℕ) := certificate_532_part_4_E

noncomputable def certificate_532_part_6_E : List (ℕ × ℕ) := certificate_532_part_5_E

noncomputable def certificate_532_part_7_E : List (ℕ × ℕ) := certificate_532_part_6_E

noncomputable def certificate_532_part_16_E : List (ℕ × ℕ) := certificate_532_part_7_E

noncomputable def certificate_532_part_17_E : List (ℕ × ℕ) := certificate_532_part_16_E

noncomputable def certificate_532_part_30_E : List (ℕ × ℕ) := certificate_532_part_17_E

noncomputable def certificate_532_part_31_E : List (ℕ × ℕ) := certificate_532_part_30_E

noncomputable def certificate_532_part_34_E : List (ℕ × ℕ) := certificate_532_part_31_E

noncomputable def certificate_532_part_56_E : List (ℕ × ℕ) := certificate_532_part_34_E

noncomputable def certificate_532_part_64_E : List (ℕ × ℕ) := certificate_532_part_56_E

noncomputable def certificate_532_part_78_E : List (ℕ × ℕ) := certificate_532_part_64_E

noncomputable def certificate_532_part_90_E : List (ℕ × ℕ) := certificate_532_part_78_E

noncomputable def certificate_532_part_100_E : List (ℕ × ℕ) := certificate_532_part_90_E

noncomputable def certificate_533_q : Finset ℕ := ([0,1,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_533_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,5),(0,7),(1,2),(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_534_q : Finset ℕ := ([0,1,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_534_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,8),(1,2),(1,3),(1,5),(1,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_535_q : Finset ℕ := ([0,1,2,3,5,9] : List ℕ).toFinset
noncomputable def certificate_535_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,9),(1,2),(1,3),(1,5),(1,9),(2,3),(2,5),(2,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_536_q : Finset ℕ := ([0,1,2,3,5,10] : List ℕ).toFinset
noncomputable def certificate_536_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,10),(1,2),(1,3),(1,5),(1,10),(2,3),(2,5),(2,10),(3,5),(3,10),(5,10)]

noncomputable def certificate_537_q : Finset ℕ := ([0,1,2,3,5,11] : List ℕ).toFinset
noncomputable def certificate_537_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,11),(1,2),(1,3),(1,5),(1,11),(2,3),(2,5),(2,11),(3,5),(3,11),(5,11)]

noncomputable def certificate_538_q : Finset ℕ := ([0,1,2,3,5,12] : List ℕ).toFinset

noncomputable def certificate_538_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,12),(1,2),(1,3),(1,5),(1,12),(2,3),(2,5),(2,12),(3,5),(3,12),(5,12)]

noncomputable def certificate_538_E : List (ℕ × ℕ) := certificate_538_edges

noncomputable def certificate_538_part_1_E : List (ℕ × ℕ) := certificate_538_E

noncomputable def certificate_538_part_2_E : List (ℕ × ℕ) := certificate_538_part_1_E

noncomputable def certificate_538_part_3_E : List (ℕ × ℕ) := certificate_538_part_2_E

noncomputable def certificate_538_part_4_E : List (ℕ × ℕ) := certificate_538_part_3_E

noncomputable def certificate_538_part_5_E : List (ℕ × ℕ) := certificate_538_part_4_E

noncomputable def certificate_538_part_6_E : List (ℕ × ℕ) := certificate_538_part_5_E

noncomputable def certificate_538_part_7_E : List (ℕ × ℕ) := certificate_538_part_6_E

noncomputable def certificate_538_part_8_E : List (ℕ × ℕ) := certificate_538_part_7_E

noncomputable def certificate_538_part_9_E : List (ℕ × ℕ) := certificate_538_part_8_E

noncomputable def certificate_538_part_10_E : List (ℕ × ℕ) := certificate_538_part_9_E

noncomputable def certificate_538_part_11_E : List (ℕ × ℕ) := certificate_538_part_10_E

noncomputable def certificate_538_part_12_E : List (ℕ × ℕ) := certificate_538_part_11_E

noncomputable def certificate_538_part_14_E : List (ℕ × ℕ) := certificate_538_part_12_E

noncomputable def certificate_538_part_15_E : List (ℕ × ℕ) := certificate_538_part_14_E

noncomputable def certificate_538_part_28_E : List (ℕ × ℕ) := certificate_538_part_15_E

noncomputable def certificate_538_part_34_E : List (ℕ × ℕ) := certificate_538_part_28_E

noncomputable def certificate_538_part_43_E : List (ℕ × ℕ) := certificate_538_part_34_E

noncomputable def certificate_538_part_50_E : List (ℕ × ℕ) := certificate_538_part_43_E

noncomputable def certificate_538_part_51_E : List (ℕ × ℕ) := certificate_538_part_50_E

noncomputable def certificate_538_part_52_E : List (ℕ × ℕ) := certificate_538_part_51_E

noncomputable def certificate_539_q : Finset ℕ := ([0,1,2,3,6,9] : List ℕ).toFinset
noncomputable def certificate_539_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,6),(0,9),(1,2),(1,3),(1,6),(1,9),(2,3),(2,6),(2,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_540_q : Finset ℕ := ([0,1,2,3,6,10] : List ℕ).toFinset
noncomputable def certificate_540_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,10),(1,2),(1,3),(1,6),(1,10),(2,3),(2,6),(2,10),(3,6),(3,10),(6,10)]

noncomputable def certificate_541_q : Finset ℕ := ([0,1,2,3,6,11] : List ℕ).toFinset
noncomputable def certificate_541_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,11),(1,2),(1,3),(1,6),(1,11),(2,3),(2,6),(2,11),(3,6),(3,11),(6,11)]

noncomputable def certificate_542_q : Finset ℕ := ([0,1,2,3,6,12] : List ℕ).toFinset
noncomputable def certificate_542_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,12),(1,2),(1,3),(1,6),(1,12),(2,3),(2,6),(2,12),(3,6),(3,12),(6,12)]

noncomputable def certificate_543_q : Finset ℕ := ([0,1,2,3,7,11] : List ℕ).toFinset
noncomputable def certificate_543_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,7),(0,11),(1,2),(1,3),(1,7),(1,11),(2,3),(2,7),(2,11),(3,7),(3,11),(7,11)]

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

noncomputable def certificate_544_q : Finset ℕ := ([0,1,2,3,7,12] : List ℕ).toFinset

noncomputable def certificate_544_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,7),(0,12),(1,2),(1,3),(1,7),(1,12),(2,3),(2,7),(2,12),(3,7),(3,12),(7,12)]

noncomputable def certificate_544_E : List (ℕ × ℕ) := certificate_544_edges

noncomputable def certificate_544_part_1_E : List (ℕ × ℕ) := certificate_544_E

noncomputable def certificate_544_part_2_E : List (ℕ × ℕ) := certificate_544_part_1_E

noncomputable def certificate_544_part_3_E : List (ℕ × ℕ) := certificate_544_part_2_E

noncomputable def certificate_544_part_4_E : List (ℕ × ℕ) := certificate_544_part_3_E

noncomputable def certificate_544_part_5_E : List (ℕ × ℕ) := certificate_544_part_4_E

noncomputable def certificate_544_part_6_E : List (ℕ × ℕ) := certificate_544_part_5_E

noncomputable def certificate_544_part_7_E : List (ℕ × ℕ) := certificate_544_part_6_E

noncomputable def certificate_544_part_9_E : List (ℕ × ℕ) := certificate_544_part_7_E

noncomputable def certificate_544_part_11_E : List (ℕ × ℕ) := certificate_544_part_9_E

noncomputable def certificate_544_part_12_E : List (ℕ × ℕ) := certificate_544_part_11_E

noncomputable def certificate_544_part_16_E : List (ℕ × ℕ) := certificate_544_part_12_E

noncomputable def certificate_544_part_17_E : List (ℕ × ℕ) := certificate_544_part_16_E

noncomputable def certificate_544_part_18_E : List (ℕ × ℕ) := certificate_544_part_17_E

noncomputable def certificate_544_part_19_E : List (ℕ × ℕ) := certificate_544_part_18_E

noncomputable def certificate_544_part_20_E : List (ℕ × ℕ) := certificate_544_part_19_E

noncomputable def certificate_544_part_25_E : List (ℕ × ℕ) := certificate_544_part_20_E

noncomputable def certificate_544_part_27_E : List (ℕ × ℕ) := certificate_544_part_25_E

noncomputable def certificate_544_part_29_E : List (ℕ × ℕ) := certificate_544_part_27_E

noncomputable def certificate_544_part_34_E : List (ℕ × ℕ) := certificate_544_part_29_E

noncomputable def certificate_544_part_37_E : List (ℕ × ℕ) := certificate_544_part_34_E

noncomputable def certificate_545_q : Finset ℕ := ([0,1,2,4,5,7] : List ℕ).toFinset
noncomputable def certificate_545_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(0,1),(0,2),(0,4),(0,5),(0,7),(1,2),(1,4),(1,5),(1,7),(2,4),(2,5),(2,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_546_q : Finset ℕ := ([0,1,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_546_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,5),(0,8),(1,2),(1,4),(1,5),(1,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_547_q : Finset ℕ := ([0,1,2,4,5,9] : List ℕ).toFinset
noncomputable def certificate_547_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,9),(1,2),(1,4),(1,5),(1,9),(2,4),(2,5),(2,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_548_q : Finset ℕ := ([0,1,2,4,5,10] : List ℕ).toFinset
noncomputable def certificate_548_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,10),(1,2),(1,4),(1,5),(1,10),(2,4),(2,5),(2,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_549_q : Finset ℕ := ([0,1,2,4,5,11] : List ℕ).toFinset
noncomputable def certificate_549_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,11),(1,2),(1,4),(1,5),(1,11),(2,4),(2,5),(2,11),(4,5),(4,11),(5,11)]

noncomputable def certificate_550_q : Finset ℕ := ([0,1,2,4,5,12] : List ℕ).toFinset

noncomputable def certificate_550_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,12),(1,2),(1,4),(1,5),(1,12),(2,4),(2,5),(2,12),(4,5),(4,12),(5,12)]

noncomputable def certificate_550_E : List (ℕ × ℕ) := certificate_550_edges

noncomputable def certificate_550_part_1_E : List (ℕ × ℕ) := certificate_550_E

noncomputable def certificate_550_part_2_E : List (ℕ × ℕ) := certificate_550_part_1_E

noncomputable def certificate_550_part_3_E : List (ℕ × ℕ) := certificate_550_part_2_E

noncomputable def certificate_550_part_4_E : List (ℕ × ℕ) := certificate_550_part_3_E

noncomputable def certificate_550_part_5_E : List (ℕ × ℕ) := certificate_550_part_4_E

noncomputable def certificate_550_part_6_E : List (ℕ × ℕ) := certificate_550_part_5_E

noncomputable def certificate_550_part_7_E : List (ℕ × ℕ) := certificate_550_part_6_E

noncomputable def certificate_550_part_8_E : List (ℕ × ℕ) := certificate_550_part_7_E

noncomputable def certificate_550_part_9_E : List (ℕ × ℕ) := certificate_550_part_8_E

noncomputable def certificate_550_part_10_E : List (ℕ × ℕ) := certificate_550_part_9_E

noncomputable def certificate_550_part_11_E : List (ℕ × ℕ) := certificate_550_part_10_E

noncomputable def certificate_550_part_12_E : List (ℕ × ℕ) := certificate_550_part_11_E

noncomputable def certificate_550_part_14_E : List (ℕ × ℕ) := certificate_550_part_12_E

noncomputable def certificate_550_part_15_E : List (ℕ × ℕ) := certificate_550_part_14_E

noncomputable def certificate_550_part_28_E : List (ℕ × ℕ) := certificate_550_part_15_E

noncomputable def certificate_550_part_34_E : List (ℕ × ℕ) := certificate_550_part_28_E

noncomputable def certificate_550_part_43_E : List (ℕ × ℕ) := certificate_550_part_34_E

noncomputable def certificate_550_part_54_E : List (ℕ × ℕ) := certificate_550_part_43_E

noncomputable def certificate_551_q : Finset ℕ := ([0,1,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_551_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,6),(0,8),(1,2),(1,4),(1,6),(1,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_552_q : Finset ℕ := ([0,1,2,4,6,9] : List ℕ).toFinset
noncomputable def certificate_552_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,6),(0,9),(1,2),(1,4),(1,6),(1,9),(2,4),(2,6),(2,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_553_q : Finset ℕ := ([0,1,2,4,6,10] : List ℕ).toFinset
noncomputable def certificate_553_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,10),(1,2),(1,4),(1,6),(1,10),(2,4),(2,6),(2,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_554_q : Finset ℕ := ([0,1,2,4,6,11] : List ℕ).toFinset
noncomputable def certificate_554_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,11),(1,2),(1,4),(1,6),(1,11),(2,4),(2,6),(2,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_555_q : Finset ℕ := ([0,1,2,4,6,12] : List ℕ).toFinset
noncomputable def certificate_555_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,12),(1,2),(1,4),(1,6),(1,12),(2,4),(2,6),(2,12),(4,6),(4,12),(6,12)]

noncomputable def certificate_556_q : Finset ℕ := ([0,1,2,4,7,9] : List ℕ).toFinset
noncomputable def certificate_556_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,7),(0,9),(1,2),(1,4),(1,7),(1,9),(2,4),(2,7),(2,9),(4,7),(4,9),(7,9)]

noncomputable def certificate_557_q : Finset ℕ := ([0,1,2,4,7,10] : List ℕ).toFinset
noncomputable def certificate_557_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,7),(0,10),(1,2),(1,4),(1,7),(1,10),(2,4),(2,7),(2,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_558_q : Finset ℕ := ([0,1,2,4,7,11] : List ℕ).toFinset
noncomputable def certificate_558_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,7),(0,11),(1,2),(1,4),(1,7),(1,11),(2,4),(2,7),(2,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_559_q : Finset ℕ := ([0,1,2,4,7,12] : List ℕ).toFinset
noncomputable def certificate_559_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,12),(1,2),(1,4),(1,7),(1,12),(2,4),(2,7),(2,12),(4,7),(4,12),(7,12)]

noncomputable def certificate_560_q : Finset ℕ := ([0,1,2,4,8,10] : List ℕ).toFinset
noncomputable def certificate_560_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,8),(0,10),(1,2),(1,4),(1,8),(1,10),(2,4),(2,8),(2,10),(4,8),(4,10),(8,10)]

noncomputable def certificate_561_q : Finset ℕ := ([0,1,2,4,8,11] : List ℕ).toFinset
noncomputable def certificate_561_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,8),(0,11),(1,2),(1,4),(1,8),(1,11),(2,4),(2,8),(2,11),(4,8),(4,11),(8,11)]

noncomputable def certificate_562_q : Finset ℕ := ([0,1,2,4,8,12] : List ℕ).toFinset
noncomputable def certificate_562_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,8),(0,12),(1,2),(1,4),(1,8),(1,12),(2,4),(2,8),(2,12),(4,8),(4,12),(8,12)]

noncomputable def certificate_563_q : Finset ℕ := ([0,1,2,4,9,11] : List ℕ).toFinset
noncomputable def certificate_563_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,9),(0,11),(1,2),(1,4),(1,9),(1,11),(2,4),(2,9),(2,11),(4,9),(4,11),(9,11)]

noncomputable def certificate_564_q : Finset ℕ := ([0,1,2,4,9,12] : List ℕ).toFinset
noncomputable def certificate_564_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,9),(0,12),(1,2),(1,4),(1,9),(1,12),(2,4),(2,9),(2,12),(4,9),(4,12),(9,12)]

noncomputable def certificate_565_q : Finset ℕ := ([0,1,2,4,10,12] : List ℕ).toFinset
noncomputable def certificate_565_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,10),(0,12),(1,2),(1,4),(1,10),(1,12),(2,4),(2,10),(2,12),(4,10),(4,12),(10,12)]

noncomputable def certificate_566_q : Finset ℕ := ([0,1,2,5,6,9] : List ℕ).toFinset
noncomputable def certificate_566_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,5),(0,6),(0,9),(1,2),(1,5),(1,6),(1,9),(2,5),(2,6),(2,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_567_q : Finset ℕ := ([0,1,2,5,6,10] : List ℕ).toFinset
noncomputable def certificate_567_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,6),(0,10),(1,2),(1,5),(1,6),(1,10),(2,5),(2,6),(2,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_568_q : Finset ℕ := ([0,1,2,5,6,11] : List ℕ).toFinset
noncomputable def certificate_568_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,5),(0,6),(0,11),(1,2),(1,5),(1,6),(1,11),(2,5),(2,6),(2,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_569_q : Finset ℕ := ([0,1,2,5,6,12] : List ℕ).toFinset

noncomputable def certificate_569_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,6),(0,12),(1,2),(1,5),(1,6),(1,12),(2,5),(2,6),(2,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_569_E : List (ℕ × ℕ) := certificate_569_edges

noncomputable def certificate_569_part_1_E : List (ℕ × ℕ) := certificate_569_E

noncomputable def certificate_569_part_2_E : List (ℕ × ℕ) := certificate_569_part_1_E

noncomputable def certificate_569_part_3_E : List (ℕ × ℕ) := certificate_569_part_2_E

noncomputable def certificate_569_part_4_E : List (ℕ × ℕ) := certificate_569_part_3_E

noncomputable def certificate_569_part_5_E : List (ℕ × ℕ) := certificate_569_part_4_E

noncomputable def certificate_569_part_6_E : List (ℕ × ℕ) := certificate_569_part_5_E

noncomputable def certificate_569_part_7_E : List (ℕ × ℕ) := certificate_569_part_6_E

noncomputable def certificate_569_part_8_E : List (ℕ × ℕ) := certificate_569_part_7_E

noncomputable def certificate_569_part_9_E : List (ℕ × ℕ) := certificate_569_part_8_E

noncomputable def certificate_569_part_10_E : List (ℕ × ℕ) := certificate_569_part_9_E

noncomputable def certificate_569_part_12_E : List (ℕ × ℕ) := certificate_569_part_10_E

noncomputable def certificate_569_part_13_E : List (ℕ × ℕ) := certificate_569_part_12_E

noncomputable def certificate_569_part_14_E : List (ℕ × ℕ) := certificate_569_part_13_E

noncomputable def certificate_569_part_15_E : List (ℕ × ℕ) := certificate_569_part_14_E

noncomputable def certificate_569_part_16_E : List (ℕ × ℕ) := certificate_569_part_15_E

noncomputable def certificate_569_part_18_E : List (ℕ × ℕ) := certificate_569_part_16_E

noncomputable def certificate_569_part_19_E : List (ℕ × ℕ) := certificate_569_part_18_E

noncomputable def certificate_569_part_23_E : List (ℕ × ℕ) := certificate_569_part_19_E

noncomputable def certificate_569_part_24_E : List (ℕ × ℕ) := certificate_569_part_23_E

noncomputable def certificate_569_part_27_E : List (ℕ × ℕ) := certificate_569_part_24_E

noncomputable def certificate_569_part_29_E : List (ℕ × ℕ) := certificate_569_part_27_E

noncomputable def certificate_570_q : Finset ℕ := ([0,1,2,5,7,10] : List ℕ).toFinset
noncomputable def certificate_570_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,7),(0,10),(1,2),(1,5),(1,7),(1,10),(2,5),(2,7),(2,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_571_q : Finset ℕ := ([0,1,2,5,7,11] : List ℕ).toFinset
noncomputable def certificate_571_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,5),(0,7),(0,11),(1,2),(1,5),(1,7),(1,11),(2,5),(2,7),(2,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_572_q : Finset ℕ := ([0,1,2,5,7,12] : List ℕ).toFinset
noncomputable def certificate_572_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,7),(0,12),(1,2),(1,5),(1,7),(1,12),(2,5),(2,7),(2,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_573_q : Finset ℕ := ([0,1,2,5,8,11] : List ℕ).toFinset
noncomputable def certificate_573_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,5),(0,8),(0,11),(1,2),(1,5),(1,8),(1,11),(2,5),(2,8),(2,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_574_q : Finset ℕ := ([0,1,2,5,8,12] : List ℕ).toFinset
noncomputable def certificate_574_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,8),(0,12),(1,2),(1,5),(1,8),(1,12),(2,5),(2,8),(2,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_575_q : Finset ℕ := ([0,1,2,5,9,12] : List ℕ).toFinset
noncomputable def certificate_575_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,9),(0,12),(1,2),(1,5),(1,9),(1,12),(2,5),(2,9),(2,12),(5,9),(5,12),(9,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates019
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_576_q : Finset ℕ := ([0,1,2,6,7,11] : List ℕ).toFinset
noncomputable def certificate_576_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,6),(0,7),(0,11),(1,2),(1,6),(1,7),(1,11),(2,6),(2,7),(2,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_577_q : Finset ℕ := ([0,1,2,6,7,12] : List ℕ).toFinset

noncomputable def certificate_577_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,6),(0,7),(0,12),(1,2),(1,6),(1,7),(1,12),(2,6),(2,7),(2,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_577_E : List (ℕ × ℕ) := certificate_577_edges

noncomputable def certificate_577_part_1_E : List (ℕ × ℕ) := certificate_577_E

noncomputable def certificate_577_part_2_E : List (ℕ × ℕ) := certificate_577_part_1_E

noncomputable def certificate_577_part_3_E : List (ℕ × ℕ) := certificate_577_part_2_E

noncomputable def certificate_577_part_4_E : List (ℕ × ℕ) := certificate_577_part_3_E

noncomputable def certificate_577_part_5_E : List (ℕ × ℕ) := certificate_577_part_4_E

noncomputable def certificate_577_part_6_E : List (ℕ × ℕ) := certificate_577_part_5_E

noncomputable def certificate_577_part_7_E : List (ℕ × ℕ) := certificate_577_part_6_E

noncomputable def certificate_577_part_9_E : List (ℕ × ℕ) := certificate_577_part_7_E

noncomputable def certificate_577_part_10_E : List (ℕ × ℕ) := certificate_577_part_9_E

noncomputable def certificate_577_part_11_E : List (ℕ × ℕ) := certificate_577_part_10_E

noncomputable def certificate_577_part_12_E : List (ℕ × ℕ) := certificate_577_part_11_E

noncomputable def certificate_577_part_13_E : List (ℕ × ℕ) := certificate_577_part_12_E

noncomputable def certificate_577_part_15_E : List (ℕ × ℕ) := certificate_577_part_13_E

noncomputable def certificate_577_part_16_E : List (ℕ × ℕ) := certificate_577_part_15_E

noncomputable def certificate_577_part_17_E : List (ℕ × ℕ) := certificate_577_part_16_E

noncomputable def certificate_577_part_18_E : List (ℕ × ℕ) := certificate_577_part_17_E

noncomputable def certificate_577_part_22_E : List (ℕ × ℕ) := certificate_577_part_18_E

noncomputable def certificate_577_part_23_E : List (ℕ × ℕ) := certificate_577_part_22_E

noncomputable def certificate_577_part_24_E : List (ℕ × ℕ) := certificate_577_part_23_E

noncomputable def certificate_577_part_25_E : List (ℕ × ℕ) := certificate_577_part_24_E

noncomputable def certificate_577_part_30_E : List (ℕ × ℕ) := certificate_577_part_25_E

noncomputable def certificate_577_part_32_E : List (ℕ × ℕ) := certificate_577_part_30_E

noncomputable def certificate_577_part_33_E : List (ℕ × ℕ) := certificate_577_part_32_E

noncomputable def certificate_577_part_34_E : List (ℕ × ℕ) := certificate_577_part_33_E

noncomputable def certificate_577_part_35_E : List (ℕ × ℕ) := certificate_577_part_34_E

noncomputable def certificate_577_part_37_E : List (ℕ × ℕ) := certificate_577_part_35_E

noncomputable def certificate_577_part_39_E : List (ℕ × ℕ) := certificate_577_part_37_E

noncomputable def certificate_577_part_45_E : List (ℕ × ℕ) := certificate_577_part_39_E

noncomputable def certificate_577_part_48_E : List (ℕ × ℕ) := certificate_577_part_45_E

noncomputable def certificate_578_q : Finset ℕ := ([0,1,2,6,8,12] : List ℕ).toFinset
noncomputable def certificate_578_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,6),(0,8),(0,12),(1,2),(1,6),(1,8),(1,12),(2,6),(2,8),(2,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_579_q : Finset ℕ := ([0,1,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_579_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,6),(0,8),(1,3),(1,4),(1,6),(1,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_580_q : Finset ℕ := ([0,1,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_580_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,9),(1,3),(1,4),(1,6),(1,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_581_q : Finset ℕ := ([0,1,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_581_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,10),(1,3),(1,4),(1,6),(1,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_582_q : Finset ℕ := ([0,1,3,4,6,11] : List ℕ).toFinset
noncomputable def certificate_582_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,11),(1,3),(1,4),(1,6),(1,11),(3,4),(3,6),(3,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_583_q : Finset ℕ := ([0,1,3,4,6,12] : List ℕ).toFinset
noncomputable def certificate_583_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,12),(1,3),(1,4),(1,6),(1,12),(3,4),(3,6),(3,12),(4,6),(4,12),(6,12)]

noncomputable def certificate_584_q : Finset ℕ := ([0,1,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_584_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,7),(0,10),(1,3),(1,4),(1,7),(1,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_585_q : Finset ℕ := ([0,1,3,4,7,11] : List ℕ).toFinset
noncomputable def certificate_585_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,7),(0,11),(1,3),(1,4),(1,7),(1,11),(3,4),(3,7),(3,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_586_q : Finset ℕ := ([0,1,3,4,7,12] : List ℕ).toFinset
noncomputable def certificate_586_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,12),(1,3),(1,4),(1,7),(1,12),(3,4),(3,7),(3,12),(4,7),(4,12),(7,12)]

noncomputable def certificate_587_q : Finset ℕ := ([0,1,3,4,8,12] : List ℕ).toFinset
noncomputable def certificate_587_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,8),(0,12),(1,3),(1,4),(1,8),(1,12),(3,4),(3,8),(3,12),(4,8),(4,12),(8,12)]

noncomputable def certificate_588_q : Finset ℕ := ([0,1,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_588_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,6),(0,9),(1,3),(1,5),(1,6),(1,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_589_q : Finset ℕ := ([0,1,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_589_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,10),(1,3),(1,5),(1,6),(1,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_590_q : Finset ℕ := ([0,1,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_590_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,6),(0,11),(1,3),(1,5),(1,6),(1,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_591_q : Finset ℕ := ([0,1,3,5,6,12] : List ℕ).toFinset
noncomputable def certificate_591_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,12),(1,3),(1,5),(1,6),(1,12),(3,5),(3,6),(3,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_592_q : Finset ℕ := ([0,1,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_592_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,7),(0,9),(1,3),(1,5),(1,7),(1,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_593_q : Finset ℕ := ([0,1,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_593_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,7),(0,10),(1,3),(1,5),(1,7),(1,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_594_q : Finset ℕ := ([0,1,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_594_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,11),(1,3),(1,5),(1,7),(1,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_595_q : Finset ℕ := ([0,1,3,5,7,12] : List ℕ).toFinset
noncomputable def certificate_595_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,12),(1,3),(1,5),(1,7),(1,12),(3,5),(3,7),(3,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_596_q : Finset ℕ := ([0,1,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_596_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,8),(0,10),(1,3),(1,5),(1,8),(1,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_597_q : Finset ℕ := ([0,1,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_597_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,8),(0,11),(1,3),(1,5),(1,8),(1,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_598_q : Finset ℕ := ([0,1,3,5,8,12] : List ℕ).toFinset
noncomputable def certificate_598_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,12),(1,3),(1,5),(1,8),(1,12),(3,5),(3,8),(3,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_599_q : Finset ℕ := ([0,1,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_599_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,9),(0,11),(1,3),(1,5),(1,9),(1,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_600_q : Finset ℕ := ([0,1,3,5,9,12] : List ℕ).toFinset
noncomputable def certificate_600_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,9),(0,12),(1,3),(1,5),(1,9),(1,12),(3,5),(3,9),(3,12),(5,9),(5,12),(9,12)]

noncomputable def certificate_601_q : Finset ℕ := ([0,1,3,5,10,12] : List ℕ).toFinset
noncomputable def certificate_601_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,10),(0,12),(1,3),(1,5),(1,10),(1,12),(3,5),(3,10),(3,12),(5,10),(5,12),(10,12)]

noncomputable def certificate_602_q : Finset ℕ := ([0,1,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_602_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,6),(0,7),(0,10),(1,3),(1,6),(1,7),(1,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_603_q : Finset ℕ := ([0,1,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_603_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,6),(0,7),(0,11),(1,3),(1,6),(1,7),(1,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_604_q : Finset ℕ := ([0,1,3,6,7,12] : List ℕ).toFinset
noncomputable def certificate_604_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,7),(0,12),(1,3),(1,6),(1,7),(1,12),(3,6),(3,7),(3,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_605_q : Finset ℕ := ([0,1,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_605_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,6),(0,8),(0,11),(1,3),(1,6),(1,8),(1,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_606_q : Finset ℕ := ([0,1,3,6,8,12] : List ℕ).toFinset
noncomputable def certificate_606_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,8),(0,12),(1,3),(1,6),(1,8),(1,12),(3,6),(3,8),(3,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_607_q : Finset ℕ := ([0,1,3,6,9,11] : List ℕ).toFinset
noncomputable def certificate_607_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,6),(0,9),(0,11),(1,3),(1,6),(1,9),(1,11),(3,6),(3,9),(3,11),(6,9),(6,11),(9,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates020
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_608_q : Finset ℕ := ([0,1,3,6,9,12] : List ℕ).toFinset
noncomputable def certificate_608_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,9),(0,12),(1,3),(1,6),(1,9),(1,12),(3,6),(3,9),(3,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_609_q : Finset ℕ := ([0,1,3,6,10,12] : List ℕ).toFinset
noncomputable def certificate_609_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,10),(0,12),(1,3),(1,6),(1,10),(1,12),(3,6),(3,10),(3,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_610_q : Finset ℕ := ([0,1,3,7,8,11] : List ℕ).toFinset
noncomputable def certificate_610_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,7),(0,8),(0,11),(1,3),(1,7),(1,8),(1,11),(3,7),(3,8),(3,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_611_q : Finset ℕ := ([0,1,3,7,8,12] : List ℕ).toFinset
noncomputable def certificate_611_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,7),(0,8),(0,12),(1,3),(1,7),(1,8),(1,12),(3,7),(3,8),(3,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_612_q : Finset ℕ := ([0,1,3,7,9,12] : List ℕ).toFinset
noncomputable def certificate_612_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,7),(0,9),(0,12),(1,3),(1,7),(1,9),(1,12),(3,7),(3,9),(3,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_613_q : Finset ℕ := ([0,1,3,8,9,12] : List ℕ).toFinset
noncomputable def certificate_613_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,8),(0,9),(0,12),(1,3),(1,8),(1,9),(1,12),(3,8),(3,9),(3,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_614_q : Finset ℕ := ([0,1,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_614_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,4),(0,5),(0,8),(0,11),(1,4),(1,5),(1,8),(1,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_615_q : Finset ℕ := ([0,1,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_615_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,4),(0,5),(0,8),(0,12),(1,4),(1,5),(1,8),(1,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_616_q : Finset ℕ := ([0,1,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_616_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,4),(0,6),(0,8),(0,11),(1,4),(1,6),(1,8),(1,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_617_q : Finset ℕ := ([0,1,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_617_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,4),(0,6),(0,8),(0,12),(1,4),(1,6),(1,8),(1,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_618_q : Finset ℕ := ([0,1,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_618_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,4),(0,6),(0,9),(0,12),(1,4),(1,6),(1,9),(1,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_619_q : Finset ℕ := ([0,1,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_619_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,4),(0,7),(0,8),(0,12),(1,4),(1,7),(1,8),(1,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_620_q : Finset ℕ := ([0,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_620_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(0,2),(0,3),(0,5),(0,6),(0,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_621_q : Finset ℕ := ([0,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_621_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,6),(0,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_622_q : Finset ℕ := ([0,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_622_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_623_q : Finset ℕ := ([0,2,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_623_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,11),(2,3),(2,5),(2,6),(2,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_624_q : Finset ℕ := ([0,2,3,5,6,12] : List ℕ).toFinset
noncomputable def certificate_624_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,12),(2,3),(2,5),(2,6),(2,12),(3,5),(3,6),(3,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_625_q : Finset ℕ := ([0,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_625_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,7),(0,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_626_q : Finset ℕ := ([0,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_626_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,7),(0,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_627_q : Finset ℕ := ([0,2,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_627_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,11),(2,3),(2,5),(2,7),(2,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_628_q : Finset ℕ := ([0,2,3,5,7,12] : List ℕ).toFinset
noncomputable def certificate_628_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,12),(2,3),(2,5),(2,7),(2,12),(3,5),(3,7),(3,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_629_q : Finset ℕ := ([0,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_629_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,8),(0,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_630_q : Finset ℕ := ([0,2,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_630_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,8),(0,11),(2,3),(2,5),(2,8),(2,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_631_q : Finset ℕ := ([0,2,3,5,8,12] : List ℕ).toFinset
noncomputable def certificate_631_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,8),(0,12),(2,3),(2,5),(2,8),(2,12),(3,5),(3,8),(3,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_632_q : Finset ℕ := ([0,2,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_632_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,9),(0,11),(2,3),(2,5),(2,9),(2,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_633_q : Finset ℕ := ([0,2,3,5,9,12] : List ℕ).toFinset
noncomputable def certificate_633_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,9),(0,12),(2,3),(2,5),(2,9),(2,12),(3,5),(3,9),(3,12),(5,9),(5,12),(9,12)]

noncomputable def certificate_634_q : Finset ℕ := ([0,2,3,5,10,12] : List ℕ).toFinset
noncomputable def certificate_634_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,10),(0,12),(2,3),(2,5),(2,10),(2,12),(3,5),(3,10),(3,12),(5,10),(5,12),(10,12)]

noncomputable def certificate_635_q : Finset ℕ := ([0,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_635_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,3),(0,6),(0,7),(0,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_636_q : Finset ℕ := ([0,2,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_636_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,6),(0,7),(0,11),(2,3),(2,6),(2,7),(2,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_637_q : Finset ℕ := ([0,2,3,6,7,12] : List ℕ).toFinset
noncomputable def certificate_637_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,6),(0,7),(0,12),(2,3),(2,6),(2,7),(2,12),(3,6),(3,7),(3,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_638_q : Finset ℕ := ([0,2,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_638_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,6),(0,8),(0,11),(2,3),(2,6),(2,8),(2,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_639_q : Finset ℕ := ([0,2,3,6,8,12] : List ℕ).toFinset
noncomputable def certificate_639_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,6),(0,8),(0,12),(2,3),(2,6),(2,8),(2,12),(3,6),(3,8),(3,12),(6,8),(6,12),(8,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates021
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_640_q : Finset ℕ := ([0,2,3,6,9,12] : List ℕ).toFinset
noncomputable def certificate_640_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,6),(0,9),(0,12),(2,3),(2,6),(2,9),(2,12),(3,6),(3,9),(3,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_641_q : Finset ℕ := ([0,2,3,7,8,12] : List ℕ).toFinset
noncomputable def certificate_641_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,7),(0,8),(0,12),(2,3),(2,7),(2,8),(2,12),(3,7),(3,8),(3,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_642_q : Finset ℕ := ([0,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_642_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,5),(0,7),(0,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_643_q : Finset ℕ := ([0,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_643_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,5),(0,7),(0,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_644_q : Finset ℕ := ([0,2,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_644_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,7),(0,11),(2,4),(2,5),(2,7),(2,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_645_q : Finset ℕ := ([0,2,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_645_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,12),(2,4),(2,5),(2,7),(2,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_646_q : Finset ℕ := ([0,2,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_646_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,8),(0,11),(2,4),(2,5),(2,8),(2,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_647_q : Finset ℕ := ([0,2,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_647_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,8),(0,12),(2,4),(2,5),(2,8),(2,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_648_q : Finset ℕ := ([0,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_648_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,7),(0,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_649_q : Finset ℕ := ([0,2,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_649_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,6),(0,7),(0,11),(2,4),(2,6),(2,7),(2,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_650_q : Finset ℕ := ([0,2,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_650_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,7),(0,12),(2,4),(2,6),(2,7),(2,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_651_q : Finset ℕ := ([0,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_651_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,2),(0,4),(0,6),(0,8),(0,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_652_q : Finset ℕ := ([0,2,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_652_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,6),(0,8),(0,11),(2,4),(2,6),(2,8),(2,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_653_q : Finset ℕ := ([0,2,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_653_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,12),(2,4),(2,6),(2,8),(2,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_654_q : Finset ℕ := ([0,2,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_654_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,6),(0,9),(0,11),(2,4),(2,6),(2,9),(2,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_655_q : Finset ℕ := ([0,2,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_655_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,9),(0,12),(2,4),(2,6),(2,9),(2,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_656_q : Finset ℕ := ([0,2,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_656_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,10),(0,12),(2,4),(2,6),(2,10),(2,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_657_q : Finset ℕ := ([0,2,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_657_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,4),(0,7),(0,8),(0,11),(2,4),(2,7),(2,8),(2,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_658_q : Finset ℕ := ([0,2,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_658_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,7),(0,8),(0,12),(2,4),(2,7),(2,8),(2,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_659_q : Finset ℕ := ([0,2,4,7,9,11] : List ℕ).toFinset
noncomputable def certificate_659_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,7),(0,9),(0,11),(2,4),(2,7),(2,9),(2,11),(4,7),(4,9),(4,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_660_q : Finset ℕ := ([0,2,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_660_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,7),(0,9),(0,12),(2,4),(2,7),(2,9),(2,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_661_q : Finset ℕ := ([0,2,4,7,10,12] : List ℕ).toFinset
noncomputable def certificate_661_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,7),(0,10),(0,12),(2,4),(2,7),(2,10),(2,12),(4,7),(4,10),(4,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_662_q : Finset ℕ := ([0,2,4,8,9,12] : List ℕ).toFinset
noncomputable def certificate_662_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,8),(0,9),(0,12),(2,4),(2,8),(2,9),(2,12),(4,8),(4,9),(4,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_663_q : Finset ℕ := ([0,2,4,8,10,12] : List ℕ).toFinset
noncomputable def certificate_663_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,8),(0,10),(0,12),(2,4),(2,8),(2,10),(2,12),(4,8),(4,10),(4,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_664_q : Finset ℕ := ([0,2,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_664_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,5),(0,6),(0,8),(0,11),(2,5),(2,6),(2,8),(2,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_665_q : Finset ℕ := ([0,2,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_665_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,5),(0,6),(0,8),(0,12),(2,5),(2,6),(2,8),(2,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_666_q : Finset ℕ := ([0,2,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_666_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,5),(0,6),(0,9),(0,12),(2,5),(2,6),(2,9),(2,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_667_q : Finset ℕ := ([0,2,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_667_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,5),(0,7),(0,8),(0,11),(2,5),(2,7),(2,8),(2,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_668_q : Finset ℕ := ([0,2,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_668_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,5),(0,7),(0,8),(0,12),(2,5),(2,7),(2,8),(2,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_669_q : Finset ℕ := ([0,2,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_669_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,5),(0,7),(0,9),(0,12),(2,5),(2,7),(2,9),(2,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_670_q : Finset ℕ := ([0,2,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_670_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,5),(0,7),(0,10),(0,12),(2,5),(2,7),(2,10),(2,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_671_q : Finset ℕ := ([0,2,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_671_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,5),(0,8),(0,9),(0,12),(2,5),(2,8),(2,9),(2,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates022
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_672_q : Finset ℕ := ([0,2,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_672_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,6),(0,8),(0,9),(0,12),(2,6),(2,8),(2,9),(2,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_673_q : Finset ℕ := ([0,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_673_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,3),(0,4),(0,7),(0,8),(0,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_674_q : Finset ℕ := ([0,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_674_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,3),(0,4),(0,7),(0,8),(0,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_675_q : Finset ℕ := ([0,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_675_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,3),(0,4),(0,7),(0,9),(0,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_676_q : Finset ℕ := ([0,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_676_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,3),(0,5),(0,7),(0,9),(0,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_677_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_677_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_678_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_678_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_679_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_679_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_680_q : Finset ℕ := ([0,1,2,3,4,5,9] : List ℕ).toFinset
noncomputable def certificate_680_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(1,2),(1,3),(1,4),(1,5),(1,9),(2,3),(2,4),(2,5),(2,9),(3,4),(3,5),(3,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_681_q : Finset ℕ := ([0,1,2,3,4,5,10] : List ℕ).toFinset
noncomputable def certificate_681_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(1,2),(1,3),(1,4),(1,5),(1,10),(2,3),(2,4),(2,5),(2,10),(3,4),(3,5),(3,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_682_q : Finset ℕ := ([0,1,2,3,4,5,11] : List ℕ).toFinset
noncomputable def certificate_682_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,11),(1,2),(1,3),(1,4),(1,5),(1,11),(2,3),(2,4),(2,5),(2,11),(3,4),(3,5),(3,11),(4,5),(4,11),(5,11)]

noncomputable def certificate_683_q : Finset ℕ := ([0,1,2,3,4,5,12] : List ℕ).toFinset
noncomputable def certificate_683_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,12),(1,2),(1,3),(1,4),(1,5),(1,12),(2,3),(2,4),(2,5),(2,12),(3,4),(3,5),(3,12),(4,5),(4,12),(5,12)]

noncomputable def certificate_684_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_684_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_685_q : Finset ℕ := ([0,1,2,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_685_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(1,2),(1,3),(1,4),(1,6),(1,9),(2,3),(2,4),(2,6),(2,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_686_q : Finset ℕ := ([0,1,2,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_686_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(1,2),(1,3),(1,4),(1,6),(1,10),(2,3),(2,4),(2,6),(2,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_687_q : Finset ℕ := ([0,1,2,3,4,6,11] : List ℕ).toFinset
noncomputable def certificate_687_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(1,2),(1,3),(1,4),(1,6),(1,11),(2,3),(2,4),(2,6),(2,11),(3,4),(3,6),(3,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_688_q : Finset ℕ := ([0,1,2,3,4,6,12] : List ℕ).toFinset
noncomputable def certificate_688_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(1,2),(1,3),(1,4),(1,6),(1,12),(2,3),(2,4),(2,6),(2,12),(3,4),(3,6),(3,12),(4,6),(4,12),(6,12)]

noncomputable def certificate_689_q : Finset ℕ := ([0,1,2,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_689_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(1,2),(1,3),(1,4),(1,7),(1,10),(2,3),(2,4),(2,7),(2,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_690_q : Finset ℕ := ([0,1,2,3,4,7,11] : List ℕ).toFinset
noncomputable def certificate_690_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(1,2),(1,3),(1,4),(1,7),(1,11),(2,3),(2,4),(2,7),(2,11),(3,4),(3,7),(3,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_691_q : Finset ℕ := ([0,1,2,3,4,7,12] : List ℕ).toFinset
noncomputable def certificate_691_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,12),(1,2),(1,3),(1,4),(1,7),(1,12),(2,3),(2,4),(2,7),(2,12),(3,4),(3,7),(3,12),(4,7),(4,12),(7,12)]

noncomputable def certificate_692_q : Finset ℕ := ([0,1,2,3,4,8,12] : List ℕ).toFinset
noncomputable def certificate_692_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,8),(0,12),(1,2),(1,3),(1,4),(1,8),(1,12),(2,3),(2,4),(2,8),(2,12),(3,4),(3,8),(3,12),(4,8),(4,12),(8,12)]

noncomputable def certificate_693_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_693_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_694_q : Finset ℕ := ([0,1,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_694_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(1,2),(1,3),(1,5),(1,6),(1,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_695_q : Finset ℕ := ([0,1,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_695_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(1,2),(1,3),(1,5),(1,6),(1,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_696_q : Finset ℕ := ([0,1,2,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_696_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,11),(1,2),(1,3),(1,5),(1,6),(1,11),(2,3),(2,5),(2,6),(2,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_697_q : Finset ℕ := ([0,1,2,3,5,6,12] : List ℕ).toFinset
noncomputable def certificate_697_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,12),(1,2),(1,3),(1,5),(1,6),(1,12),(2,3),(2,5),(2,6),(2,12),(3,5),(3,6),(3,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_698_q : Finset ℕ := ([0,1,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_698_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(1,2),(1,3),(1,5),(1,7),(1,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_699_q : Finset ℕ := ([0,1,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_699_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(1,2),(1,3),(1,5),(1,7),(1,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_700_q : Finset ℕ := ([0,1,2,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_700_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(1,2),(1,3),(1,5),(1,7),(1,11),(2,3),(2,5),(2,7),(2,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_701_q : Finset ℕ := ([0,1,2,3,5,7,12] : List ℕ).toFinset
noncomputable def certificate_701_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(1,2),(1,3),(1,5),(1,7),(1,12),(2,3),(2,5),(2,7),(2,12),(3,5),(3,7),(3,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_702_q : Finset ℕ := ([0,1,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_702_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(1,2),(1,3),(1,5),(1,8),(1,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_703_q : Finset ℕ := ([0,1,2,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_703_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(1,2),(1,3),(1,5),(1,8),(1,11),(2,3),(2,5),(2,8),(2,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates023
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_704_q : Finset ℕ := ([0,1,2,3,5,8,12] : List ℕ).toFinset
noncomputable def certificate_704_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(1,2),(1,3),(1,5),(1,8),(1,12),(2,3),(2,5),(2,8),(2,12),(3,5),(3,8),(3,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_705_q : Finset ℕ := ([0,1,2,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_705_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(1,2),(1,3),(1,5),(1,9),(1,11),(2,3),(2,5),(2,9),(2,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_706_q : Finset ℕ := ([0,1,2,3,5,9,12] : List ℕ).toFinset
noncomputable def certificate_706_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,9),(0,12),(1,2),(1,3),(1,5),(1,9),(1,12),(2,3),(2,5),(2,9),(2,12),(3,5),(3,9),(3,12),(5,9),(5,12),(9,12)]

noncomputable def certificate_707_q : Finset ℕ := ([0,1,2,3,5,10,12] : List ℕ).toFinset
noncomputable def certificate_707_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,10),(0,12),(1,2),(1,3),(1,5),(1,10),(1,12),(2,3),(2,5),(2,10),(2,12),(3,5),(3,10),(3,12),(5,10),(5,12),(10,12)]

noncomputable def certificate_708_q : Finset ℕ := ([0,1,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_708_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(1,2),(1,3),(1,6),(1,7),(1,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_709_q : Finset ℕ := ([0,1,2,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_709_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(1,2),(1,3),(1,6),(1,7),(1,11),(2,3),(2,6),(2,7),(2,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_710_q : Finset ℕ := ([0,1,2,3,6,7,12] : List ℕ).toFinset
noncomputable def certificate_710_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,7),(0,12),(1,2),(1,3),(1,6),(1,7),(1,12),(2,3),(2,6),(2,7),(2,12),(3,6),(3,7),(3,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_711_q : Finset ℕ := ([0,1,2,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_711_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(1,2),(1,3),(1,6),(1,8),(1,11),(2,3),(2,6),(2,8),(2,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_712_q : Finset ℕ := ([0,1,2,3,6,8,12] : List ℕ).toFinset
noncomputable def certificate_712_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(1,2),(1,3),(1,6),(1,8),(1,12),(2,3),(2,6),(2,8),(2,12),(3,6),(3,8),(3,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_713_q : Finset ℕ := ([0,1,2,3,6,9,12] : List ℕ).toFinset
noncomputable def certificate_713_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,9),(0,12),(1,2),(1,3),(1,6),(1,9),(1,12),(2,3),(2,6),(2,9),(2,12),(3,6),(3,9),(3,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_714_q : Finset ℕ := ([0,1,2,3,7,8,12] : List ℕ).toFinset
noncomputable def certificate_714_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,7),(0,8),(0,12),(1,2),(1,3),(1,7),(1,8),(1,12),(2,3),(2,7),(2,8),(2,12),(3,7),(3,8),(3,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_715_q : Finset ℕ := ([0,1,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_715_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(1,2),(1,4),(1,5),(1,7),(1,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_716_q : Finset ℕ := ([0,1,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_716_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(1,2),(1,4),(1,5),(1,7),(1,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_717_q : Finset ℕ := ([0,1,2,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_717_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(1,2),(1,4),(1,5),(1,7),(1,11),(2,4),(2,5),(2,7),(2,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_718_q : Finset ℕ := ([0,1,2,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_718_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(1,2),(1,4),(1,5),(1,7),(1,12),(2,4),(2,5),(2,7),(2,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_719_q : Finset ℕ := ([0,1,2,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_719_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(1,2),(1,4),(1,5),(1,8),(1,11),(2,4),(2,5),(2,8),(2,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_720_q : Finset ℕ := ([0,1,2,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_720_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,12),(1,2),(1,4),(1,5),(1,8),(1,12),(2,4),(2,5),(2,8),(2,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_721_q : Finset ℕ := ([0,1,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_721_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(1,2),(1,4),(1,6),(1,7),(1,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_722_q : Finset ℕ := ([0,1,2,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_722_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(1,2),(1,4),(1,6),(1,7),(1,11),(2,4),(2,6),(2,7),(2,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_723_q : Finset ℕ := ([0,1,2,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_723_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,12),(1,2),(1,4),(1,6),(1,7),(1,12),(2,4),(2,6),(2,7),(2,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_724_q : Finset ℕ := ([0,1,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_724_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(1,2),(1,4),(1,6),(1,8),(1,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_725_q : Finset ℕ := ([0,1,2,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_725_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(1,2),(1,4),(1,6),(1,8),(1,11),(2,4),(2,6),(2,8),(2,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_726_q : Finset ℕ := ([0,1,2,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_726_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(1,2),(1,4),(1,6),(1,8),(1,12),(2,4),(2,6),(2,8),(2,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_727_q : Finset ℕ := ([0,1,2,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_727_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(1,2),(1,4),(1,6),(1,9),(1,11),(2,4),(2,6),(2,9),(2,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_728_q : Finset ℕ := ([0,1,2,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_728_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(1,2),(1,4),(1,6),(1,9),(1,12),(2,4),(2,6),(2,9),(2,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_729_q : Finset ℕ := ([0,1,2,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_729_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(1,2),(1,4),(1,6),(1,10),(1,12),(2,4),(2,6),(2,10),(2,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_730_q : Finset ℕ := ([0,1,2,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_730_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(1,2),(1,4),(1,7),(1,8),(1,11),(2,4),(2,7),(2,8),(2,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_731_q : Finset ℕ := ([0,1,2,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_731_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,8),(0,12),(1,2),(1,4),(1,7),(1,8),(1,12),(2,4),(2,7),(2,8),(2,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_732_q : Finset ℕ := ([0,1,2,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_732_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(1,2),(1,4),(1,7),(1,9),(1,12),(2,4),(2,7),(2,9),(2,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_733_q : Finset ℕ := ([0,1,2,4,7,10,12] : List ℕ).toFinset
noncomputable def certificate_733_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,10),(0,12),(1,2),(1,4),(1,7),(1,10),(1,12),(2,4),(2,7),(2,10),(2,12),(4,7),(4,10),(4,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_734_q : Finset ℕ := ([0,1,2,4,8,9,12] : List ℕ).toFinset
noncomputable def certificate_734_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,8),(0,9),(0,12),(1,2),(1,4),(1,8),(1,9),(1,12),(2,4),(2,8),(2,9),(2,12),(4,8),(4,9),(4,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_735_q : Finset ℕ := ([0,1,2,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_735_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,6),(0,9),(0,12),(1,2),(1,5),(1,6),(1,9),(1,12),(2,5),(2,6),(2,9),(2,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates024
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_736_q : Finset ℕ := ([0,1,2,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_736_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,7),(0,9),(0,12),(1,2),(1,5),(1,7),(1,9),(1,12),(2,5),(2,7),(2,9),(2,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_737_q : Finset ℕ := ([0,1,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_737_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(1,3),(1,4),(1,6),(1,7),(1,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_738_q : Finset ℕ := ([0,1,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_738_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(1,3),(1,4),(1,6),(1,7),(1,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_739_q : Finset ℕ := ([0,1,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_739_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(1,3),(1,4),(1,6),(1,7),(1,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_740_q : Finset ℕ := ([0,1,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_740_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,12),(1,3),(1,4),(1,6),(1,7),(1,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_741_q : Finset ℕ := ([0,1,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_741_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(1,3),(1,4),(1,6),(1,8),(1,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_742_q : Finset ℕ := ([0,1,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_742_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(1,3),(1,4),(1,6),(1,8),(1,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_743_q : Finset ℕ := ([0,1,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_743_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(1,3),(1,4),(1,6),(1,8),(1,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_744_q : Finset ℕ := ([0,1,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_744_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(1,3),(1,4),(1,6),(1,9),(1,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_745_q : Finset ℕ := ([0,1,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_745_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(1,3),(1,4),(1,6),(1,9),(1,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_746_q : Finset ℕ := ([0,1,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_746_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,10),(0,12),(1,3),(1,4),(1,6),(1,10),(1,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_747_q : Finset ℕ := ([0,1,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_747_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(1,3),(1,4),(1,7),(1,8),(1,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_748_q : Finset ℕ := ([0,1,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_748_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,8),(0,12),(1,3),(1,4),(1,7),(1,8),(1,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_749_q : Finset ℕ := ([0,1,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_749_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,9),(0,12),(1,3),(1,4),(1,7),(1,9),(1,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_750_q : Finset ℕ := ([0,1,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_750_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(1,3),(1,5),(1,6),(1,8),(1,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_751_q : Finset ℕ := ([0,1,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_751_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(1,3),(1,5),(1,6),(1,8),(1,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_752_q : Finset ℕ := ([0,1,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_752_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(1,3),(1,5),(1,6),(1,8),(1,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_753_q : Finset ℕ := ([0,1,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_753_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,9),(0,12),(1,3),(1,5),(1,6),(1,9),(1,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_754_q : Finset ℕ := ([0,1,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_754_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(1,3),(1,5),(1,7),(1,8),(1,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_755_q : Finset ℕ := ([0,1,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_755_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,8),(0,12),(1,3),(1,5),(1,7),(1,8),(1,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_756_q : Finset ℕ := ([0,1,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_756_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(1,3),(1,5),(1,7),(1,9),(1,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_757_q : Finset ℕ := ([0,1,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_757_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(1,3),(1,5),(1,7),(1,9),(1,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_758_q : Finset ℕ := ([0,1,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_758_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(1,3),(1,5),(1,7),(1,10),(1,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_759_q : Finset ℕ := ([0,1,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_759_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,9),(0,12),(1,3),(1,5),(1,8),(1,9),(1,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_760_q : Finset ℕ := ([0,1,3,5,8,10,12] : List ℕ).toFinset
noncomputable def certificate_760_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,10),(0,12),(1,3),(1,5),(1,8),(1,10),(1,12),(3,5),(3,8),(3,10),(3,12),(5,8),(5,10),(5,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_761_q : Finset ℕ := ([0,1,3,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_761_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(1,3),(1,6),(1,7),(1,9),(1,12),(3,6),(3,7),(3,9),(3,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_762_q : Finset ℕ := ([0,1,3,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_762_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,8),(0,9),(0,12),(1,3),(1,6),(1,8),(1,9),(1,12),(3,6),(3,8),(3,9),(3,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_763_q : Finset ℕ := ([0,1,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_763_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,4),(0,5),(0,8),(0,9),(0,12),(1,4),(1,5),(1,8),(1,9),(1,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_764_q : Finset ℕ := ([0,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_764_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_765_q : Finset ℕ := ([0,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_765_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_766_q : Finset ℕ := ([0,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_766_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_767_q : Finset ℕ := ([0,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_767_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates025
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_768_q : Finset ℕ := ([0,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_768_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_769_q : Finset ℕ := ([0,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_769_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_770_q : Finset ℕ := ([0,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_770_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_771_q : Finset ℕ := ([0,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_771_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_772_q : Finset ℕ := ([0,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_772_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_773_q : Finset ℕ := ([0,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_773_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_774_q : Finset ℕ := ([0,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_774_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_775_q : Finset ℕ := ([0,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_775_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_776_q : Finset ℕ := ([0,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_776_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_777_q : Finset ℕ := ([0,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_777_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_778_q : Finset ℕ := ([0,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_778_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_779_q : Finset ℕ := ([0,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_779_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_780_q : Finset ℕ := ([0,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_780_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_781_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_781_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_782_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_782_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_783_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_783_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_784_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_784_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_785_q : Finset ℕ := ([0,1,2,3,4,5,6,11] : List ℕ).toFinset
noncomputable def certificate_785_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,11),(1,2),(1,3),(1,4),(1,5),(1,6),(1,11),(2,3),(2,4),(2,5),(2,6),(2,11),(3,4),(3,5),(3,6),(3,11),(4,5),(4,6),(4,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_786_q : Finset ℕ := ([0,1,2,3,4,5,6,12] : List ℕ).toFinset
noncomputable def certificate_786_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,12),(1,2),(1,3),(1,4),(1,5),(1,6),(1,12),(2,3),(2,4),(2,5),(2,6),(2,12),(3,4),(3,5),(3,6),(3,12),(4,5),(4,6),(4,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_787_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_787_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_788_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_788_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_789_q : Finset ℕ := ([0,1,2,3,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_789_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,11),(1,2),(1,3),(1,4),(1,5),(1,7),(1,11),(2,3),(2,4),(2,5),(2,7),(2,11),(3,4),(3,5),(3,7),(3,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_790_q : Finset ℕ := ([0,1,2,3,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_790_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,12),(1,2),(1,3),(1,4),(1,5),(1,7),(1,12),(2,3),(2,4),(2,5),(2,7),(2,12),(3,4),(3,5),(3,7),(3,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_791_q : Finset ℕ := ([0,1,2,3,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_791_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,11),(1,2),(1,3),(1,4),(1,5),(1,8),(1,11),(2,3),(2,4),(2,5),(2,8),(2,11),(3,4),(3,5),(3,8),(3,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_792_q : Finset ℕ := ([0,1,2,3,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_792_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,12),(1,2),(1,3),(1,4),(1,5),(1,8),(1,12),(2,3),(2,4),(2,5),(2,8),(2,12),(3,4),(3,5),(3,8),(3,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_793_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_793_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_794_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_794_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_795_q : Finset ℕ := ([0,1,2,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_795_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,11),(1,2),(1,3),(1,4),(1,6),(1,7),(1,11),(2,3),(2,4),(2,6),(2,7),(2,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_796_q : Finset ℕ := ([0,1,2,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_796_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,12),(1,2),(1,3),(1,4),(1,6),(1,7),(1,12),(2,3),(2,4),(2,6),(2,7),(2,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_797_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_797_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_798_q : Finset ℕ := ([0,1,2,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_798_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,11),(1,2),(1,3),(1,4),(1,6),(1,8),(1,11),(2,3),(2,4),(2,6),(2,8),(2,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_799_q : Finset ℕ := ([0,1,2,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_799_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,12),(1,2),(1,3),(1,4),(1,6),(1,8),(1,12),(2,3),(2,4),(2,6),(2,8),(2,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates026
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_800_q : Finset ℕ := ([0,1,2,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_800_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,11),(1,2),(1,3),(1,4),(1,6),(1,9),(1,11),(2,3),(2,4),(2,6),(2,9),(2,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_801_q : Finset ℕ := ([0,1,2,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_801_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,12),(1,2),(1,3),(1,4),(1,6),(1,9),(1,12),(2,3),(2,4),(2,6),(2,9),(2,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_802_q : Finset ℕ := ([0,1,2,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_802_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,12),(1,2),(1,3),(1,4),(1,6),(1,10),(1,12),(2,3),(2,4),(2,6),(2,10),(2,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_803_q : Finset ℕ := ([0,1,2,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_803_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,11),(1,2),(1,3),(1,4),(1,7),(1,8),(1,11),(2,3),(2,4),(2,7),(2,8),(2,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_804_q : Finset ℕ := ([0,1,2,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_804_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,12),(1,2),(1,3),(1,4),(1,7),(1,8),(1,12),(2,3),(2,4),(2,7),(2,8),(2,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_805_q : Finset ℕ := ([0,1,2,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_805_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,12),(1,2),(1,3),(1,4),(1,7),(1,9),(1,12),(2,3),(2,4),(2,7),(2,9),(2,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_806_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_806_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_807_q : Finset ℕ := ([0,1,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_807_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(1,2),(1,3),(1,5),(1,6),(1,8),(1,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_808_q : Finset ℕ := ([0,1,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_808_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(1,2),(1,3),(1,5),(1,6),(1,8),(1,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_809_q : Finset ℕ := ([0,1,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_809_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(1,2),(1,3),(1,5),(1,6),(1,9),(1,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_810_q : Finset ℕ := ([0,1,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_810_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(1,2),(1,3),(1,5),(1,7),(1,8),(1,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_811_q : Finset ℕ := ([0,1,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_811_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(1,2),(1,3),(1,5),(1,7),(1,8),(1,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_812_q : Finset ℕ := ([0,1,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_812_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(1,2),(1,3),(1,5),(1,7),(1,9),(1,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_813_q : Finset ℕ := ([0,1,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_813_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(1,2),(1,3),(1,5),(1,7),(1,9),(1,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_814_q : Finset ℕ := ([0,1,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_814_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(1,2),(1,3),(1,5),(1,7),(1,10),(1,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_815_q : Finset ℕ := ([0,1,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_815_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(1,2),(1,3),(1,5),(1,8),(1,9),(1,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_816_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset

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

noncomputable def certificate_3068_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,9),(0,12),(0,14),(0,16),(2,4),(2,7),(2,9),(2,12),(2,14),(2,16),(4,7),(4,9),(4,12),(4,14),(4,16),(7,9),(7,12),(7,14),(7,16),(9,12),(9,14),(9,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_3069_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,10),(0,11),(0,13),(0,16),(2,4),(2,7),(2,10),(2,11),(2,13),(2,16),(4,7),(4,10),(4,11),(4,13),(4,16),(7,10),(7,11),(7,13),(7,16),(10,11),(10,13),(10,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3070_q : Finset ℕ := ([0,2,4,7,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3070_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,7),(0,10),(0,12),(0,13),(0,16),(2,4),(2,7),(2,10),(2,12),(2,13),(2,16),(4,7),(4,10),(4,12),(4,13),(4,16),(7,10),(7,12),(7,13),(7,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3071_q : Finset ℕ := ([0,2,4,8,9,11,14,16] : List ℕ).toFinset
noncomputable def certificate_3071_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,8),(0,9),(0,11),(0,14),(0,16),(2,4),(2,8),(2,9),(2,11),(2,14),(2,16),(4,8),(4,9),(4,11),(4,14),(4,16),(8,9),(8,11),(8,14),(8,16),(9,11),(9,14),(9,16),(11,14),(11,16),(14,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates097
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_3072_q : Finset ℕ := ([0,2,4,8,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3072_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,8),(0,9),(0,12),(0,13),(0,16),(2,4),(2,8),(2,9),(2,12),(2,13),(2,16),(4,8),(4,9),(4,12),(4,13),(4,16),(8,9),(8,12),(8,13),(8,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3073_q : Finset ℕ := ([0,2,4,8,10,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3073_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,4),(0,8),(0,10),(0,11),(0,13),(0,16),(2,4),(2,8),(2,10),(2,11),(2,13),(2,16),(4,8),(4,10),(4,11),(4,13),(4,16),(8,10),(8,11),(8,13),(8,16),(10,11),(10,13),(10,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3074_q : Finset ℕ := ([0,2,4,8,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3074_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,4),(0,8),(0,10),(0,12),(0,13),(0,16),(2,4),(2,8),(2,10),(2,12),(2,13),(2,16),(4,8),(4,10),(4,12),(4,13),(4,16),(8,10),(8,12),(8,13),(8,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3075_q : Finset ℕ := ([0,2,5,6,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3075_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,5),(0,6),(0,8),(0,11),(0,12),(0,15),(2,5),(2,6),(2,8),(2,11),(2,12),(2,15),(5,6),(5,8),(5,11),(5,12),(5,15),(6,8),(6,11),(6,12),(6,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3076_q : Finset ℕ := ([0,2,5,6,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3076_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,6),(0,8),(0,11),(0,12),(0,16),(2,5),(2,6),(2,8),(2,11),(2,12),(2,16),(5,6),(5,8),(5,11),(5,12),(5,16),(6,8),(6,11),(6,12),(6,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3077_q : Finset ℕ := ([0,2,5,6,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3077_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,6),(0,8),(0,11),(0,13),(0,16),(2,5),(2,6),(2,8),(2,11),(2,13),(2,16),(5,6),(5,8),(5,11),(5,13),(5,16),(6,8),(6,11),(6,13),(6,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3078_q : Finset ℕ := ([0,2,5,6,8,11,14,16] : List ℕ).toFinset
noncomputable def certificate_3078_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,6),(0,8),(0,11),(0,14),(0,16),(2,5),(2,6),(2,8),(2,11),(2,14),(2,16),(5,6),(5,8),(5,11),(5,14),(5,16),(6,8),(6,11),(6,14),(6,16),(8,11),(8,14),(8,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_3079_q : Finset ℕ := ([0,2,5,6,8,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3079_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,5),(0,6),(0,8),(0,12),(0,13),(0,16),(2,5),(2,6),(2,8),(2,12),(2,13),(2,16),(5,6),(5,8),(5,12),(5,13),(5,16),(6,8),(6,12),(6,13),(6,16),(8,12),(8,13),(8,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3080_q : Finset ℕ := ([0,2,5,6,9,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3080_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(0,16),(2,5),(2,6),(2,9),(2,10),(2,13),(2,16),(5,6),(5,9),(5,10),(5,13),(5,16),(6,9),(6,10),(6,13),(6,16),(9,10),(9,13),(9,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3081_q : Finset ℕ := ([0,2,5,6,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3081_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,6),(0,9),(0,11),(0,13),(0,16),(2,5),(2,6),(2,9),(2,11),(2,13),(2,16),(5,6),(5,9),(5,11),(5,13),(5,16),(6,9),(6,11),(6,13),(6,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3082_q : Finset ℕ := ([0,2,5,7,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_3082_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,5),(0,7),(0,8),(0,10),(0,13),(0,15),(2,5),(2,7),(2,8),(2,10),(2,13),(2,15),(5,7),(5,8),(5,10),(5,13),(5,15),(7,8),(7,10),(7,13),(7,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_3083_q : Finset ℕ := ([0,2,5,7,8,10,13,16] : List ℕ).toFinset
noncomputable def certificate_3083_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,8),(0,10),(0,13),(0,16),(2,5),(2,7),(2,8),(2,10),(2,13),(2,16),(5,7),(5,8),(5,10),(5,13),(5,16),(7,8),(7,10),(7,13),(7,16),(8,10),(8,13),(8,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_3084_q : Finset ℕ := ([0,2,5,7,8,10,14,16] : List ℕ).toFinset
noncomputable def certificate_3084_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,8),(0,10),(0,14),(0,16),(2,5),(2,7),(2,8),(2,10),(2,14),(2,16),(5,7),(5,8),(5,10),(5,14),(5,16),(7,8),(7,10),(7,14),(7,16),(8,10),(8,14),(8,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_3085_q : Finset ℕ := ([0,2,5,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3085_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,5),(0,7),(0,8),(0,11),(0,12),(0,15),(2,5),(2,7),(2,8),(2,11),(2,12),(2,15),(5,7),(5,8),(5,11),(5,12),(5,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3086_q : Finset ℕ := ([0,2,5,7,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3086_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,8),(0,11),(0,12),(0,16),(2,5),(2,7),(2,8),(2,11),(2,12),(2,16),(5,7),(5,8),(5,11),(5,12),(5,16),(7,8),(7,11),(7,12),(7,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3087_q : Finset ℕ := ([0,2,5,7,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3087_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,8),(0,11),(0,13),(0,16),(2,5),(2,7),(2,8),(2,11),(2,13),(2,16),(5,7),(5,8),(5,11),(5,13),(5,16),(7,8),(7,11),(7,13),(7,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3088_q : Finset ℕ := ([0,2,5,7,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3088_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,9),(0,11),(0,13),(0,16),(2,5),(2,7),(2,9),(2,11),(2,13),(2,16),(5,7),(5,9),(5,11),(5,13),(5,16),(7,9),(7,11),(7,13),(7,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3089_q : Finset ℕ := ([0,2,5,7,9,11,14,16] : List ℕ).toFinset
noncomputable def certificate_3089_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,9),(0,11),(0,14),(0,16),(2,5),(2,7),(2,9),(2,11),(2,14),(2,16),(5,7),(5,9),(5,11),(5,14),(5,16),(7,9),(7,11),(7,14),(7,16),(9,11),(9,14),(9,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_3090_q : Finset ℕ := ([0,2,5,7,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3090_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,9),(0,12),(0,13),(0,16),(2,5),(2,7),(2,9),(2,12),(2,13),(2,16),(5,7),(5,9),(5,12),(5,13),(5,16),(7,9),(7,12),(7,13),(7,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3091_q : Finset ℕ := ([0,2,5,7,10,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3091_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,5),(0,7),(0,10),(0,12),(0,13),(0,16),(2,5),(2,7),(2,10),(2,12),(2,13),(2,16),(5,7),(5,10),(5,12),(5,13),(5,16),(7,10),(7,12),(7,13),(7,16),(10,12),(10,13),(10,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3092_q : Finset ℕ := ([0,2,5,8,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3092_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,5),(0,8),(0,9),(0,12),(0,13),(0,16),(2,5),(2,8),(2,9),(2,12),(2,13),(2,16),(5,8),(5,9),(5,12),(5,13),(5,16),(8,9),(8,12),(8,13),(8,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3093_q : Finset ℕ := ([0,2,6,8,9,12,13,16] : List ℕ).toFinset
noncomputable def certificate_3093_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,2),(0,6),(0,8),(0,9),(0,12),(0,13),(0,16),(2,6),(2,8),(2,9),(2,12),(2,13),(2,16),(6,8),(6,9),(6,12),(6,13),(6,16),(8,9),(8,12),(8,13),(8,16),(9,12),(9,13),(9,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_3094_q : Finset ℕ := ([0,3,4,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_3094_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,3),(0,4),(0,7),(0,8),(0,11),(0,12),(0,15),(3,4),(3,7),(3,8),(3,11),(3,12),(3,15),(4,7),(4,8),(4,11),(4,12),(4,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_3095_q : Finset ℕ := ([0,3,4,7,8,11,12,16] : List ℕ).toFinset
noncomputable def certificate_3095_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,3),(0,4),(0,7),(0,8),(0,11),(0,12),(0,16),(3,4),(3,7),(3,8),(3,11),(3,12),(3,16),(4,7),(4,8),(4,11),(4,12),(4,16),(7,8),(7,11),(7,12),(7,16),(8,11),(8,12),(8,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_3096_q : Finset ℕ := ([0,3,4,7,8,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3096_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,3),(0,4),(0,7),(0,8),(0,11),(0,13),(0,16),(3,4),(3,7),(3,8),(3,11),(3,13),(3,16),(4,7),(4,8),(4,11),(4,13),(4,16),(7,8),(7,11),(7,13),(7,16),(8,11),(8,13),(8,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3097_q : Finset ℕ := ([0,3,4,7,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3097_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,3),(0,4),(0,7),(0,9),(0,11),(0,13),(0,16),(3,4),(3,7),(3,9),(3,11),(3,13),(3,16),(4,7),(4,9),(4,11),(4,13),(4,16),(7,9),(7,11),(7,13),(7,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_3098_q : Finset ℕ := ([0,3,5,7,9,11,13,16] : List ℕ).toFinset
noncomputable def certificate_3098_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(0,16),(3,5),(3,7),(3,9),(3,11),(3,13),(3,16),(5,7),(5,9),(5,11),(5,13),(5,16),(7,9),(7,11),(7,13),(7,16),(9,11),(9,13),(9,16),(11,13),(11,16),(13,16)]

end CycleClique

end OAI
end


