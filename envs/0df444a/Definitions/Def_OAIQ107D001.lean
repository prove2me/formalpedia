-- Prove2me | Definitions.Def_OAIQ107D001
-- name    : OAIQ107D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:37:52.083976+00:00
-- url     : https://prove2.me/theorems/cd736131-a3f6-43a1-9854-09943c9212b7
-- title:
--   Definitions bundle OAIQ107D001 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 965 declarations of OpenAI's Lean: 965 definitions. The definitions and types are `OAI.CycleClique.certificate_1019_edges`, `OAI.CycleClique.certificate_1019_q`, `OAI.CycleClique.certificate_101_q`, `OAI.CycleClique.certificate_1020_edges`, `OAI.CycleClique.certificate_1020_q`, `OAI.CycleClique.certificate_1021_edges`, `OAI.CycleClique.certificate_1021_q`, `OAI.CycleClique.certificate_1022_edges`, `OAI.CycleClique.certificate_1022_q`, `OAI.CycleClique.certificate_1023_edges`, `OAI.CycleClique.certificate_1023_q`, `OAI.CycleClique.certificate_1024_edges`, `OAI.CycleClique.certificate_1024_q`, `OAI.CycleClique.certificate_1025_edges`, `OAI.CycleClique.certificate_1025_q`, `OAI.CycleClique.certificate_1026_edges`, `OAI.CycleClique.certificate_1026_q`, `OAI.CycleClique.certificate_1027_edges`, `OAI.CycleClique.certificate_1027_q`, `OAI.CycleClique.certificate_1028_edges`, `OAI.CycleClique.certificate_1028_q`, `OAI.CycleClique.certificate_1029_edges`, `OAI.CycleClique.certificate_1029_q`, `OAI.CycleClique.certificate_102_edges`, `OAI.CycleClique.certificate_102_q`, `OAI.CycleClique.certificate_1030_edges`, `OAI.CycleClique.certificate_1030_q`, `OAI.CycleClique.certificate_1031_edges`, `OAI.CycleClique.certificate_1031_q`, `OAI.CycleClique.certificate_1032_edges`, `OAI.CycleClique.certificate_1032_q`, `OAI.CycleClique.certificate_1033_edges`, `OAI.CycleClique.certificate_1033_q`, `OAI.CycleClique.certificate_1034_edges`, `OAI.CycleClique.certificate_1034_q`, `OAI.CycleClique.certificate_1035_edges`, `OAI.CycleClique.certificate_1035_q`, `OAI.CycleClique.certificate_1036_edges`, `OAI.CycleClique.certificate_1036_q`, `OAI.CycleClique.certificate_1037_edges` and 925 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates004`, `Ramsey_CycleClique_Certificates005`, `Ramsey_CycleClique_Certificates032`, `Ramsey_CycleClique_Certificates033`, `Ramsey_CycleClique_Certificates034`, `Ramsey_CycleClique_Certificates035`, `Ramsey_CycleClique_Certificates036`, `Ramsey_CycleClique_Certificates037`, `Ramsey_CycleClique_Certificates038`, `Ramsey_CycleClique_Certificates039`, `Ramsey_CycleClique_Certificates040`, `Ramsey_CycleClique_Certificates041`, `Ramsey_CycleClique_Certificates042`, `Ramsey_CycleClique_Certificates043`, `Ramsey_CycleClique_CompactDecisions`, `Ramsey_CycleClique_Patterns9x5`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D009`, `OAIQ107D010`, `OAIQ107D011`, `OAIQ107D013`, `OAIQ107D014`, `OAIQ107D015`, `OAIQ107D016`, `OAIQ107D020`, `OAIQ107D058` and `OAIQ107D119`.
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

def compactNodupLabels : List ℕ → Bool
  | [] => true
  | a :: L => !(L.contains a) && compactNodupLabels L

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

noncomputable def certificate_10_q : Finset ℕ := ([0,1,5] : List ℕ).toFinset

noncomputable def certificate_10_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,5),(1,5)]

noncomputable def certificate_10_E : List (ℕ × ℕ) := certificate_10_edges

noncomputable def certificate_10_part_1_E : List (ℕ × ℕ) := certificate_10_E

noncomputable def certificate_10_part_3_E : List (ℕ × ℕ) := certificate_10_part_1_E

noncomputable def certificate_10_part_6_E : List (ℕ × ℕ) := certificate_10_part_3_E

noncomputable def certificate_10_part_9_E : List (ℕ × ℕ) := certificate_10_part_6_E

noncomputable def certificate_10_part_11_E : List (ℕ × ℕ) := certificate_10_part_9_E

noncomputable def certificate_11_q : Finset ℕ := ([0,2,4] : List ℕ).toFinset

noncomputable def certificate_11_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(0,2),(0,4),(2,4)]

noncomputable def certificate_11_E : List (ℕ × ℕ) := certificate_11_edges

noncomputable def certificate_11_part_1_E : List (ℕ × ℕ) := certificate_11_E

noncomputable def certificate_12_q : Finset ℕ := ([0,2,5] : List ℕ).toFinset

noncomputable def certificate_12_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,2),(0,5),(2,5)]

noncomputable def certificate_12_E : List (ℕ × ℕ) := certificate_12_edges

noncomputable def certificate_12_part_1_E : List (ℕ × ℕ) := certificate_12_E

noncomputable def certificate_12_part_2_E : List (ℕ × ℕ) := certificate_12_part_1_E

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

noncomputable def certificate_101_q : Finset ℕ := ([0,2,5,8] : List ℕ).toFinset

noncomputable def certificate_102_q : Finset ℕ := ([0,2,6,8] : List ℕ).toFinset
noncomputable def certificate_102_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,6),(0,8),(2,6),(2,8),(6,8)]

noncomputable def certificate_103_q : Finset ℕ := ([0,3,4,7] : List ℕ).toFinset
noncomputable def certificate_103_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(0,3),(0,4),(0,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_104_q : Finset ℕ := ([0,3,4,8] : List ℕ).toFinset

noncomputable def certificate_104_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,3),(0,4),(0,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_104_E : List (ℕ × ℕ) := certificate_104_edges

noncomputable def certificate_104_part_1_E : List (ℕ × ℕ) := certificate_104_E

noncomputable def certificate_104_part_2_E : List (ℕ × ℕ) := certificate_104_part_1_E

noncomputable def certificate_104_part_3_E : List (ℕ × ℕ) := certificate_104_part_2_E

noncomputable def certificate_104_part_4_E : List (ℕ × ℕ) := certificate_104_part_3_E

noncomputable def certificate_104_part_5_E : List (ℕ × ℕ) := certificate_104_part_4_E

noncomputable def certificate_104_part_6_E : List (ℕ × ℕ) := certificate_104_part_5_E

noncomputable def certificate_104_part_7_E : List (ℕ × ℕ) := certificate_104_part_6_E

noncomputable def certificate_104_part_8_E : List (ℕ × ℕ) := certificate_104_part_7_E

noncomputable def certificate_104_part_9_E : List (ℕ × ℕ) := certificate_104_part_8_E

noncomputable def certificate_104_part_10_E : List (ℕ × ℕ) := certificate_104_part_9_E

noncomputable def certificate_104_part_14_E : List (ℕ × ℕ) := certificate_104_part_10_E

noncomputable def certificate_104_part_16_E : List (ℕ × ℕ) := certificate_104_part_14_E

noncomputable def certificate_104_part_17_E : List (ℕ × ℕ) := certificate_104_part_16_E

noncomputable def certificate_104_part_20_E : List (ℕ × ℕ) := certificate_104_part_17_E

noncomputable def certificate_105_q : Finset ℕ := ([0,3,5,8] : List ℕ).toFinset
noncomputable def certificate_105_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,3),(0,5),(0,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_106_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_106_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_107_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_107_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_108_q : Finset ℕ := ([0,1,2,3,6] : List ℕ).toFinset
noncomputable def certificate_108_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_109_q : Finset ℕ := ([0,1,2,3,7] : List ℕ).toFinset
noncomputable def certificate_109_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,7),(1,2),(1,3),(1,7),(2,3),(2,7),(3,7)]

noncomputable def certificate_110_q : Finset ℕ := ([0,1,2,3,8] : List ℕ).toFinset

noncomputable def certificate_110_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,8),(1,2),(1,3),(1,8),(2,3),(2,8),(3,8)]

noncomputable def certificate_110_E : List (ℕ × ℕ) := certificate_110_edges

noncomputable def certificate_110_part_1_E : List (ℕ × ℕ) := certificate_110_E

noncomputable def certificate_110_part_2_E : List (ℕ × ℕ) := certificate_110_part_1_E

noncomputable def certificate_110_part_3_E : List (ℕ × ℕ) := certificate_110_part_2_E

noncomputable def certificate_110_part_5_E : List (ℕ × ℕ) := certificate_110_part_3_E

noncomputable def certificate_110_part_6_E : List (ℕ × ℕ) := certificate_110_part_5_E

noncomputable def certificate_110_part_13_E : List (ℕ × ℕ) := certificate_110_part_6_E

noncomputable def certificate_110_part_18_E : List (ℕ × ℕ) := certificate_110_part_13_E

noncomputable def certificate_110_part_23_E : List (ℕ × ℕ) := certificate_110_part_18_E

noncomputable def certificate_110_part_28_E : List (ℕ × ℕ) := certificate_110_part_23_E

noncomputable def certificate_110_part_30_E : List (ℕ × ℕ) := certificate_110_part_28_E

noncomputable def certificate_110_part_32_E : List (ℕ × ℕ) := certificate_110_part_30_E

noncomputable def certificate_110_part_33_E : List (ℕ × ℕ) := certificate_110_part_32_E

noncomputable def certificate_110_part_36_E : List (ℕ × ℕ) := certificate_110_part_33_E

noncomputable def certificate_111_q : Finset ℕ := ([0,1,2,4,6] : List ℕ).toFinset
noncomputable def certificate_111_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,4),(0,6),(1,2),(1,4),(1,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_112_q : Finset ℕ := ([0,1,2,4,7] : List ℕ).toFinset
noncomputable def certificate_112_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,4),(0,7),(1,2),(1,4),(1,7),(2,4),(2,7),(4,7)]

noncomputable def certificate_113_q : Finset ℕ := ([0,1,2,4,8] : List ℕ).toFinset
noncomputable def certificate_113_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,8),(1,2),(1,4),(1,8),(2,4),(2,8),(4,8)]

noncomputable def certificate_114_q : Finset ℕ := ([0,1,2,5,8] : List ℕ).toFinset
noncomputable def certificate_114_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,5),(0,8),(1,2),(1,5),(1,8),(2,5),(2,8),(5,8)]

noncomputable def certificate_115_q : Finset ℕ := ([0,1,3,4,6] : List ℕ).toFinset
noncomputable def certificate_115_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(0,1),(0,3),(0,4),(0,6),(1,3),(1,4),(1,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_116_q : Finset ℕ := ([0,1,3,4,7] : List ℕ).toFinset
noncomputable def certificate_116_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(0,1),(0,3),(0,4),(0,7),(1,3),(1,4),(1,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_117_q : Finset ℕ := ([0,1,3,4,8] : List ℕ).toFinset
noncomputable def certificate_117_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,8),(1,3),(1,4),(1,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_118_q : Finset ℕ := ([0,1,3,5,7] : List ℕ).toFinset
noncomputable def certificate_118_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,3),(0,5),(0,7),(1,3),(1,5),(1,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_119_q : Finset ℕ := ([0,1,3,5,8] : List ℕ).toFinset
noncomputable def certificate_119_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,5),(0,8),(1,3),(1,5),(1,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_120_q : Finset ℕ := ([0,1,3,6,8] : List ℕ).toFinset
noncomputable def certificate_120_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,6),(0,8),(1,3),(1,6),(1,8),(3,6),(3,8),(6,8)]

noncomputable def certificate_121_q : Finset ℕ := ([0,1,4,5,8] : List ℕ).toFinset
noncomputable def certificate_121_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,4),(0,5),(0,8),(1,4),(1,5),(1,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_122_q : Finset ℕ := ([0,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_122_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(0,2),(0,3),(0,5),(0,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_123_q : Finset ℕ := ([0,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_123_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,3),(0,5),(0,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_124_q : Finset ℕ := ([0,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_124_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(0,2),(0,4),(0,5),(0,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_125_q : Finset ℕ := ([0,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_125_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,4),(0,6),(0,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_126_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_126_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_127_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_127_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

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

noncomputable def certificate_128_q : Finset ℕ := ([0,1,2,3,4,7] : List ℕ).toFinset
noncomputable def certificate_128_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,3),(1,4),(1,7),(2,3),(2,4),(2,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_129_q : Finset ℕ := ([0,1,2,3,4,8] : List ℕ).toFinset
noncomputable def certificate_129_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,8),(1,2),(1,3),(1,4),(1,8),(2,3),(2,4),(2,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_130_q : Finset ℕ := ([0,1,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_130_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,5),(0,7),(1,2),(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_131_q : Finset ℕ := ([0,1,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_131_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,8),(1,2),(1,3),(1,5),(1,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_132_q : Finset ℕ := ([0,1,2,4,5,7] : List ℕ).toFinset
noncomputable def certificate_132_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(0,1),(0,2),(0,4),(0,5),(0,7),(1,2),(1,4),(1,5),(1,7),(2,4),(2,5),(2,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_133_q : Finset ℕ := ([0,1,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_133_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,5),(0,8),(1,2),(1,4),(1,5),(1,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_134_q : Finset ℕ := ([0,1,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_134_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,6),(0,8),(1,2),(1,4),(1,6),(1,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_135_q : Finset ℕ := ([0,1,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_135_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,6),(0,8),(1,3),(1,4),(1,6),(1,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_136_q : Finset ℕ := ([0,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_136_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(0,2),(0,3),(0,5),(0,6),(0,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates032
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1019_q : Finset ℕ := ([0,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1019_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1020_q : Finset ℕ := ([0,2,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1020_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(2,4),(2,6),(2,7),(2,9),(2,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1021_q : Finset ℕ := ([0,2,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1021_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(2,4),(2,6),(2,7),(2,10),(2,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1022_q : Finset ℕ := ([0,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1022_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1023_q : Finset ℕ := ([0,2,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1023_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,8),(0,9),(0,13),(2,4),(2,6),(2,8),(2,9),(2,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

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

noncomputable def certificate_1024_q : Finset ℕ := ([0,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1024_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1025_q : Finset ℕ := ([0,2,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1025_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(2,4),(2,6),(2,8),(2,10),(2,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1026_q : Finset ℕ := ([0,2,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1026_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(2,4),(2,6),(2,8),(2,11),(2,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1027_q : Finset ℕ := ([0,2,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1027_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(2,4),(2,6),(2,9),(2,10),(2,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1028_q : Finset ℕ := ([0,2,4,6,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1028_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(2,4),(2,6),(2,9),(2,11),(2,13),(4,6),(4,9),(4,11),(4,13),(6,9),(6,11),(6,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1029_q : Finset ℕ := ([0,2,4,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1029_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(2,4),(2,7),(2,8),(2,10),(2,13),(4,7),(4,8),(4,10),(4,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1030_q : Finset ℕ := ([0,2,4,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1030_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(2,4),(2,7),(2,9),(2,10),(2,13),(4,7),(4,9),(4,10),(4,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1031_q : Finset ℕ := ([0,2,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1031_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,5),(0,6),(0,8),(0,11),(0,13),(2,5),(2,6),(2,8),(2,11),(2,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1032_q : Finset ℕ := ([0,2,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1032_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(2,5),(2,6),(2,9),(2,10),(2,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1033_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_1033_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_1034_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_1034_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_1035_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_1035_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_1036_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_1036_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_1037_q : Finset ℕ := ([0,1,2,3,4,5,6,11] : List ℕ).toFinset
noncomputable def certificate_1037_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,11),(1,2),(1,3),(1,4),(1,5),(1,6),(1,11),(2,3),(2,4),(2,5),(2,6),(2,11),(3,4),(3,5),(3,6),(3,11),(4,5),(4,6),(4,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_1038_q : Finset ℕ := ([0,1,2,3,4,5,6,12] : List ℕ).toFinset
noncomputable def certificate_1038_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,12),(1,2),(1,3),(1,4),(1,5),(1,6),(1,12),(2,3),(2,4),(2,5),(2,6),(2,12),(3,4),(3,5),(3,6),(3,12),(4,5),(4,6),(4,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_1039_q : Finset ℕ := ([0,1,2,3,4,5,6,13] : List ℕ).toFinset
noncomputable def certificate_1039_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,13),(1,2),(1,3),(1,4),(1,5),(1,6),(1,13),(2,3),(2,4),(2,5),(2,6),(2,13),(3,4),(3,5),(3,6),(3,13),(4,5),(4,6),(4,13),(5,6),(5,13),(6,13)]

noncomputable def certificate_1040_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_1040_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_1041_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_1041_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_1042_q : Finset ℕ := ([0,1,2,3,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_1042_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,11),(1,2),(1,3),(1,4),(1,5),(1,7),(1,11),(2,3),(2,4),(2,5),(2,7),(2,11),(3,4),(3,5),(3,7),(3,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_1043_q : Finset ℕ := ([0,1,2,3,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_1043_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,12),(1,2),(1,3),(1,4),(1,5),(1,7),(1,12),(2,3),(2,4),(2,5),(2,7),(2,12),(3,4),(3,5),(3,7),(3,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_1044_q : Finset ℕ := ([0,1,2,3,4,5,7,13] : List ℕ).toFinset
noncomputable def certificate_1044_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,13),(1,2),(1,3),(1,4),(1,5),(1,7),(1,13),(2,3),(2,4),(2,5),(2,7),(2,13),(3,4),(3,5),(3,7),(3,13),(4,5),(4,7),(4,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_1045_q : Finset ℕ := ([0,1,2,3,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_1045_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,11),(1,2),(1,3),(1,4),(1,5),(1,8),(1,11),(2,3),(2,4),(2,5),(2,8),(2,11),(3,4),(3,5),(3,8),(3,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_1046_q : Finset ℕ := ([0,1,2,3,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_1046_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,12),(1,2),(1,3),(1,4),(1,5),(1,8),(1,12),(2,3),(2,4),(2,5),(2,8),(2,12),(3,4),(3,5),(3,8),(3,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_1047_q : Finset ℕ := ([0,1,2,3,4,5,8,13] : List ℕ).toFinset
noncomputable def certificate_1047_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,13),(1,2),(1,3),(1,4),(1,5),(1,8),(1,13),(2,3),(2,4),(2,5),(2,8),(2,13),(3,4),(3,5),(3,8),(3,13),(4,5),(4,8),(4,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_1048_q : Finset ℕ := ([0,1,2,3,4,5,9,13] : List ℕ).toFinset
noncomputable def certificate_1048_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,13),(1,2),(1,3),(1,4),(1,5),(1,9),(1,13),(2,3),(2,4),(2,5),(2,9),(2,13),(3,4),(3,5),(3,9),(3,13),(4,5),(4,9),(4,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_1049_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_1049_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_1050_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_1050_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_1051_q : Finset ℕ := ([0,1,2,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_1051_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,11),(1,2),(1,3),(1,4),(1,6),(1,7),(1,11),(2,3),(2,4),(2,6),(2,7),(2,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_1052_q : Finset ℕ := ([0,1,2,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_1052_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,12),(1,2),(1,3),(1,4),(1,6),(1,7),(1,12),(2,3),(2,4),(2,6),(2,7),(2,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_1053_q : Finset ℕ := ([0,1,2,3,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_1053_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,13),(1,2),(1,3),(1,4),(1,6),(1,7),(1,13),(2,3),(2,4),(2,6),(2,7),(2,13),(3,4),(3,6),(3,7),(3,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_1054_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1054_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1055_q : Finset ℕ := ([0,1,2,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1055_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,11),(1,2),(1,3),(1,4),(1,6),(1,8),(1,11),(2,3),(2,4),(2,6),(2,8),(2,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates034
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1056_q : Finset ℕ := ([0,1,2,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1056_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,12),(1,2),(1,3),(1,4),(1,6),(1,8),(1,12),(2,3),(2,4),(2,6),(2,8),(2,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1057_q : Finset ℕ := ([0,1,2,3,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1057_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,13),(1,2),(1,3),(1,4),(1,6),(1,8),(1,13),(2,3),(2,4),(2,6),(2,8),(2,13),(3,4),(3,6),(3,8),(3,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1058_q : Finset ℕ := ([0,1,2,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_1058_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,11),(1,2),(1,3),(1,4),(1,6),(1,9),(1,11),(2,3),(2,4),(2,6),(2,9),(2,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_1059_q : Finset ℕ := ([0,1,2,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1059_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,12),(1,2),(1,3),(1,4),(1,6),(1,9),(1,12),(2,3),(2,4),(2,6),(2,9),(2,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1060_q : Finset ℕ := ([0,1,2,3,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1060_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,13),(1,2),(1,3),(1,4),(1,6),(1,9),(1,13),(2,3),(2,4),(2,6),(2,9),(2,13),(3,4),(3,6),(3,9),(3,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1061_q : Finset ℕ := ([0,1,2,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_1061_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,12),(1,2),(1,3),(1,4),(1,6),(1,10),(1,12),(2,3),(2,4),(2,6),(2,10),(2,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_1062_q : Finset ℕ := ([0,1,2,3,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_1062_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,13),(1,2),(1,3),(1,4),(1,6),(1,10),(1,13),(2,3),(2,4),(2,6),(2,10),(2,13),(3,4),(3,6),(3,10),(3,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_1063_q : Finset ℕ := ([0,1,2,3,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_1063_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,13),(1,2),(1,3),(1,4),(1,6),(1,11),(1,13),(2,3),(2,4),(2,6),(2,11),(2,13),(3,4),(3,6),(3,11),(3,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_1064_q : Finset ℕ := ([0,1,2,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1064_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,11),(1,2),(1,3),(1,4),(1,7),(1,8),(1,11),(2,3),(2,4),(2,7),(2,8),(2,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1065_q : Finset ℕ := ([0,1,2,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1065_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,12),(1,2),(1,3),(1,4),(1,7),(1,8),(1,12),(2,3),(2,4),(2,7),(2,8),(2,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1066_q : Finset ℕ := ([0,1,2,3,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1066_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,13),(1,2),(1,3),(1,4),(1,7),(1,8),(1,13),(2,3),(2,4),(2,7),(2,8),(2,13),(3,4),(3,7),(3,8),(3,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1067_q : Finset ℕ := ([0,1,2,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1067_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,12),(1,2),(1,3),(1,4),(1,7),(1,9),(1,12),(2,3),(2,4),(2,7),(2,9),(2,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1068_q : Finset ℕ := ([0,1,2,3,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1068_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,13),(1,2),(1,3),(1,4),(1,7),(1,9),(1,13),(2,3),(2,4),(2,7),(2,9),(2,13),(3,4),(3,7),(3,9),(3,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1069_q : Finset ℕ := ([0,1,2,3,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1069_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,13),(1,2),(1,3),(1,4),(1,7),(1,10),(1,13),(2,3),(2,4),(2,7),(2,10),(2,13),(3,4),(3,7),(3,10),(3,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1070_q : Finset ℕ := ([0,1,2,3,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1070_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,13),(1,2),(1,3),(1,4),(1,8),(1,9),(1,13),(2,3),(2,4),(2,8),(2,9),(2,13),(3,4),(3,8),(3,9),(3,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1071_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1071_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1072_q : Finset ℕ := ([0,1,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1072_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(1,2),(1,3),(1,5),(1,6),(1,8),(1,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1073_q : Finset ℕ := ([0,1,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1073_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(1,2),(1,3),(1,5),(1,6),(1,8),(1,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1074_q : Finset ℕ := ([0,1,2,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1074_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(1,2),(1,3),(1,5),(1,6),(1,8),(1,13),(2,3),(2,5),(2,6),(2,8),(2,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1075_q : Finset ℕ := ([0,1,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1075_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(1,2),(1,3),(1,5),(1,6),(1,9),(1,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1076_q : Finset ℕ := ([0,1,2,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1076_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(1,2),(1,3),(1,5),(1,6),(1,9),(1,13),(2,3),(2,5),(2,6),(2,9),(2,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1077_q : Finset ℕ := ([0,1,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1077_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(1,2),(1,3),(1,5),(1,7),(1,8),(1,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1078_q : Finset ℕ := ([0,1,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1078_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(1,2),(1,3),(1,5),(1,7),(1,8),(1,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1079_q : Finset ℕ := ([0,1,2,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1079_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,13),(1,2),(1,3),(1,5),(1,7),(1,8),(1,13),(2,3),(2,5),(2,7),(2,8),(2,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1080_q : Finset ℕ := ([0,1,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1080_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(1,2),(1,3),(1,5),(1,7),(1,9),(1,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1081_q : Finset ℕ := ([0,1,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1081_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(1,2),(1,3),(1,5),(1,7),(1,9),(1,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1082_q : Finset ℕ := ([0,1,2,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1082_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(1,2),(1,3),(1,5),(1,7),(1,9),(1,13),(2,3),(2,5),(2,7),(2,9),(2,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1083_q : Finset ℕ := ([0,1,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1083_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(1,2),(1,3),(1,5),(1,7),(1,10),(1,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1084_q : Finset ℕ := ([0,1,2,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1084_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(1,2),(1,3),(1,5),(1,7),(1,10),(1,13),(2,3),(2,5),(2,7),(2,10),(2,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1085_q : Finset ℕ := ([0,1,2,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1085_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(1,2),(1,3),(1,5),(1,7),(1,11),(1,13),(2,3),(2,5),(2,7),(2,11),(2,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1086_q : Finset ℕ := ([0,1,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1086_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(1,2),(1,3),(1,5),(1,8),(1,9),(1,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1087_q : Finset ℕ := ([0,1,2,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1087_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,13),(1,2),(1,3),(1,5),(1,8),(1,9),(1,13),(2,3),(2,5),(2,8),(2,9),(2,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

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

noncomputable def certificate_1088_q : Finset ℕ := ([0,1,2,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1088_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(1,2),(1,3),(1,5),(1,8),(1,10),(1,13),(2,3),(2,5),(2,8),(2,10),(2,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1089_q : Finset ℕ := ([0,1,2,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1089_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(1,2),(1,3),(1,5),(1,8),(1,11),(1,13),(2,3),(2,5),(2,8),(2,11),(2,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1090_q : Finset ℕ := ([0,1,2,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1090_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(1,2),(1,3),(1,5),(1,9),(1,10),(1,13),(2,3),(2,5),(2,9),(2,10),(2,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1091_q : Finset ℕ := ([0,1,2,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1091_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(1,2),(1,3),(1,6),(1,7),(1,10),(1,13),(2,3),(2,6),(2,7),(2,10),(2,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1092_q : Finset ℕ := ([0,1,2,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1092_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(1,2),(1,3),(1,6),(1,8),(1,10),(1,13),(2,3),(2,6),(2,8),(2,10),(2,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1093_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset
noncomputable def certificate_1093_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_1094_q : Finset ℕ := ([0,1,2,4,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1094_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,11),(1,2),(1,4),(1,5),(1,7),(1,8),(1,11),(2,4),(2,5),(2,7),(2,8),(2,11),(4,5),(4,7),(4,8),(4,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1095_q : Finset ℕ := ([0,1,2,4,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1095_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,12),(1,2),(1,4),(1,5),(1,7),(1,8),(1,12),(2,4),(2,5),(2,7),(2,8),(2,12),(4,5),(4,7),(4,8),(4,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1096_q : Finset ℕ := ([0,1,2,4,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1096_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,13),(1,2),(1,4),(1,5),(1,7),(1,8),(1,13),(2,4),(2,5),(2,7),(2,8),(2,13),(4,5),(4,7),(4,8),(4,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1097_q : Finset ℕ := ([0,1,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1097_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(1,2),(1,4),(1,5),(1,7),(1,9),(1,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1098_q : Finset ℕ := ([0,1,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1098_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(1,2),(1,4),(1,5),(1,7),(1,9),(1,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1099_q : Finset ℕ := ([0,1,2,4,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1099_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(1,2),(1,4),(1,5),(1,7),(1,9),(1,13),(2,4),(2,5),(2,7),(2,9),(2,13),(4,5),(4,7),(4,9),(4,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1100_q : Finset ℕ := ([0,1,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1100_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(1,2),(1,4),(1,5),(1,7),(1,10),(1,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1101_q : Finset ℕ := ([0,1,2,4,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1101_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(1,2),(1,4),(1,5),(1,7),(1,10),(1,13),(2,4),(2,5),(2,7),(2,10),(2,13),(4,5),(4,7),(4,10),(4,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1102_q : Finset ℕ := ([0,1,2,4,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1102_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(1,2),(1,4),(1,5),(1,7),(1,11),(1,13),(2,4),(2,5),(2,7),(2,11),(2,13),(4,5),(4,7),(4,11),(4,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1103_q : Finset ℕ := ([0,1,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1103_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(1,2),(1,4),(1,5),(1,8),(1,9),(1,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1104_q : Finset ℕ := ([0,1,2,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1104_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,13),(1,2),(1,4),(1,5),(1,8),(1,9),(1,13),(2,4),(2,5),(2,8),(2,9),(2,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1105_q : Finset ℕ := ([0,1,2,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1105_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(1,2),(1,4),(1,5),(1,8),(1,10),(1,13),(2,4),(2,5),(2,8),(2,10),(2,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1106_q : Finset ℕ := ([0,1,2,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1106_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(1,2),(1,4),(1,6),(1,7),(1,9),(1,11),(2,4),(2,6),(2,7),(2,9),(2,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1107_q : Finset ℕ := ([0,1,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1107_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(1,2),(1,4),(1,6),(1,7),(1,9),(1,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1108_q : Finset ℕ := ([0,1,2,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1108_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(1,2),(1,4),(1,6),(1,7),(1,9),(1,13),(2,4),(2,6),(2,7),(2,9),(2,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1109_q : Finset ℕ := ([0,1,2,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1109_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(1,2),(1,4),(1,6),(1,7),(1,10),(1,13),(2,4),(2,6),(2,7),(2,10),(2,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1110_q : Finset ℕ := ([0,1,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1110_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(1,2),(1,4),(1,6),(1,8),(1,9),(1,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1111_q : Finset ℕ := ([0,1,2,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1111_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,13),(1,2),(1,4),(1,6),(1,8),(1,9),(1,13),(2,4),(2,6),(2,8),(2,9),(2,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1112_q : Finset ℕ := ([0,1,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1112_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(1,2),(1,4),(1,6),(1,8),(1,10),(1,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1113_q : Finset ℕ := ([0,1,2,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1113_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(1,2),(1,4),(1,6),(1,8),(1,10),(1,13),(2,4),(2,6),(2,8),(2,10),(2,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1114_q : Finset ℕ := ([0,1,2,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1114_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(1,2),(1,4),(1,6),(1,8),(1,11),(1,13),(2,4),(2,6),(2,8),(2,11),(2,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1115_q : Finset ℕ := ([0,1,2,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1115_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(1,2),(1,4),(1,6),(1,9),(1,10),(1,13),(2,4),(2,6),(2,9),(2,10),(2,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1116_q : Finset ℕ := ([0,1,2,4,6,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1116_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(1,2),(1,4),(1,6),(1,9),(1,11),(1,13),(2,4),(2,6),(2,9),(2,11),(2,13),(4,6),(4,9),(4,11),(4,13),(6,9),(6,11),(6,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1117_q : Finset ℕ := ([0,1,2,4,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1117_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(1,2),(1,4),(1,7),(1,8),(1,10),(1,13),(2,4),(2,7),(2,8),(2,10),(2,13),(4,7),(4,8),(4,10),(4,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1118_q : Finset ℕ := ([0,1,2,4,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1118_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(1,2),(1,4),(1,7),(1,9),(1,10),(1,13),(2,4),(2,7),(2,9),(2,10),(2,13),(4,7),(4,9),(4,10),(4,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1119_q : Finset ℕ := ([0,1,2,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1119_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(1,2),(1,5),(1,6),(1,9),(1,10),(1,13),(2,5),(2,6),(2,9),(2,10),(2,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

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

noncomputable def certificate_1120_q : Finset ℕ := ([0,1,3,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1120_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,11),(1,3),(1,4),(1,6),(1,7),(1,9),(1,11),(3,4),(3,6),(3,7),(3,9),(3,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1121_q : Finset ℕ := ([0,1,3,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1121_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,12),(1,3),(1,4),(1,6),(1,7),(1,9),(1,12),(3,4),(3,6),(3,7),(3,9),(3,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1122_q : Finset ℕ := ([0,1,3,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1122_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,13),(1,3),(1,4),(1,6),(1,7),(1,9),(1,13),(3,4),(3,6),(3,7),(3,9),(3,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1123_q : Finset ℕ := ([0,1,3,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1123_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,13),(1,3),(1,4),(1,6),(1,7),(1,10),(1,13),(3,4),(3,6),(3,7),(3,10),(3,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1124_q : Finset ℕ := ([0,1,3,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1124_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,12),(1,3),(1,4),(1,6),(1,8),(1,9),(1,12),(3,4),(3,6),(3,8),(3,9),(3,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1125_q : Finset ℕ := ([0,1,3,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1125_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,13),(1,3),(1,4),(1,6),(1,8),(1,9),(1,13),(3,4),(3,6),(3,8),(3,9),(3,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1126_q : Finset ℕ := ([0,1,3,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1126_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,12),(1,3),(1,4),(1,6),(1,8),(1,10),(1,12),(3,4),(3,6),(3,8),(3,10),(3,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1127_q : Finset ℕ := ([0,1,3,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1127_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,13),(1,3),(1,4),(1,6),(1,8),(1,10),(1,13),(3,4),(3,6),(3,8),(3,10),(3,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1128_q : Finset ℕ := ([0,1,3,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1128_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,13),(1,3),(1,4),(1,6),(1,8),(1,11),(1,13),(3,4),(3,6),(3,8),(3,11),(3,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1129_q : Finset ℕ := ([0,1,3,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1129_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,13),(1,3),(1,4),(1,6),(1,9),(1,10),(1,13),(3,4),(3,6),(3,9),(3,10),(3,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1130_q : Finset ℕ := ([0,1,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1130_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(1,3),(1,5),(1,6),(1,8),(1,10),(1,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1131_q : Finset ℕ := ([0,1,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1131_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(1,3),(1,5),(1,6),(1,8),(1,10),(1,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1132_q : Finset ℕ := ([0,1,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1132_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(1,3),(1,5),(1,6),(1,8),(1,11),(1,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1133_q : Finset ℕ := ([0,1,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1133_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(1,3),(1,5),(1,6),(1,9),(1,10),(1,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1134_q : Finset ℕ := ([0,1,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1134_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(1,3),(1,5),(1,7),(1,8),(1,10),(1,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1135_q : Finset ℕ := ([0,1,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1135_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(1,3),(1,5),(1,7),(1,9),(1,10),(1,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1136_q : Finset ℕ := ([0,1,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1136_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(1,3),(1,5),(1,7),(1,9),(1,11),(1,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1137_q : Finset ℕ := ([0,2,3,5,6,8,9,11] : List ℕ).toFinset
noncomputable def certificate_1137_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,11),(2,3),(2,5),(2,6),(2,8),(2,9),(2,11),(3,5),(3,6),(3,8),(3,9),(3,11),(5,6),(5,8),(5,9),(5,11),(6,8),(6,9),(6,11),(8,9),(8,11),(9,11)]

noncomputable def certificate_1138_q : Finset ℕ := ([0,2,3,5,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1138_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,12),(2,3),(2,5),(2,6),(2,8),(2,9),(2,12),(3,5),(3,6),(3,8),(3,9),(3,12),(5,6),(5,8),(5,9),(5,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1139_q : Finset ℕ := ([0,2,3,5,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1139_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,13),(2,3),(2,5),(2,6),(2,8),(2,9),(2,13),(3,5),(3,6),(3,8),(3,9),(3,13),(5,6),(5,8),(5,9),(5,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1140_q : Finset ℕ := ([0,2,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1140_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(2,3),(2,5),(2,6),(2,8),(2,10),(2,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1141_q : Finset ℕ := ([0,2,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1141_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(2,3),(2,5),(2,6),(2,8),(2,10),(2,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1142_q : Finset ℕ := ([0,2,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1142_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(2,3),(2,5),(2,6),(2,8),(2,11),(2,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1143_q : Finset ℕ := ([0,2,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1143_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(2,3),(2,5),(2,6),(2,9),(2,10),(2,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1144_q : Finset ℕ := ([0,2,3,5,7,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1144_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,12),(2,3),(2,5),(2,7),(2,8),(2,10),(2,12),(3,5),(3,7),(3,8),(3,10),(3,12),(5,7),(5,8),(5,10),(5,12),(7,8),(7,10),(7,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1145_q : Finset ℕ := ([0,2,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1145_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(2,3),(2,5),(2,7),(2,8),(2,10),(2,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1146_q : Finset ℕ := ([0,2,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1146_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(2,3),(2,5),(2,7),(2,9),(2,10),(2,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1147_q : Finset ℕ := ([0,2,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1147_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(2,3),(2,5),(2,7),(2,9),(2,11),(2,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1148_q : Finset ℕ := ([0,2,4,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1148_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,13),(2,4),(2,5),(2,7),(2,9),(2,10),(2,13),(4,5),(4,7),(4,9),(4,10),(4,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1149_q : Finset ℕ := ([0,2,4,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1149_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,13),(2,4),(2,5),(2,7),(2,9),(2,11),(2,13),(4,5),(4,7),(4,9),(4,11),(4,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1150_q : Finset ℕ := ([0,2,4,6,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1150_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,13),(2,4),(2,6),(2,7),(2,9),(2,11),(2,13),(4,6),(4,7),(4,9),(4,11),(4,13),(6,7),(6,9),(6,11),(6,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1151_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_1151_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

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

noncomputable def certificate_1152_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_1152_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_1153_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_1153_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_1154_q : Finset ℕ := ([0,1,2,3,4,5,9] : List ℕ).toFinset
noncomputable def certificate_1154_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(1,2),(1,3),(1,4),(1,5),(1,9),(2,3),(2,4),(2,5),(2,9),(3,4),(3,5),(3,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_1155_q : Finset ℕ := ([0,1,2,3,4,5,10] : List ℕ).toFinset
noncomputable def certificate_1155_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(1,2),(1,3),(1,4),(1,5),(1,10),(2,3),(2,4),(2,5),(2,10),(3,4),(3,5),(3,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_1156_q : Finset ℕ := ([0,1,2,3,4,5,11] : List ℕ).toFinset
noncomputable def certificate_1156_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,11),(1,2),(1,3),(1,4),(1,5),(1,11),(2,3),(2,4),(2,5),(2,11),(3,4),(3,5),(3,11),(4,5),(4,11),(5,11)]

noncomputable def certificate_1157_q : Finset ℕ := ([0,1,2,3,4,5,12] : List ℕ).toFinset
noncomputable def certificate_1157_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,12),(1,2),(1,3),(1,4),(1,5),(1,12),(2,3),(2,4),(2,5),(2,12),(3,4),(3,5),(3,12),(4,5),(4,12),(5,12)]

noncomputable def certificate_1158_q : Finset ℕ := ([0,1,2,3,4,5,13] : List ℕ).toFinset
noncomputable def certificate_1158_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,13),(1,2),(1,3),(1,4),(1,5),(1,13),(2,3),(2,4),(2,5),(2,13),(3,4),(3,5),(3,13),(4,5),(4,13),(5,13)]

noncomputable def certificate_1159_q : Finset ℕ := ([0,1,2,3,4,5,14] : List ℕ).toFinset

noncomputable def certificate_1159_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,14),(1,2),(1,3),(1,4),(1,5),(1,14),(2,3),(2,4),(2,5),(2,14),(3,4),(3,5),(3,14),(4,5),(4,14),(5,14)]

noncomputable def certificate_1159_E : List (ℕ × ℕ) := certificate_1159_edges

noncomputable def certificate_1159_part_1_E : List (ℕ × ℕ) := certificate_1159_E

noncomputable def certificate_1159_part_2_E : List (ℕ × ℕ) := certificate_1159_part_1_E

noncomputable def certificate_1159_part_3_E : List (ℕ × ℕ) := certificate_1159_part_2_E

noncomputable def certificate_1159_part_4_E : List (ℕ × ℕ) := certificate_1159_part_3_E

noncomputable def certificate_1159_part_5_E : List (ℕ × ℕ) := certificate_1159_part_4_E

noncomputable def certificate_1159_part_6_E : List (ℕ × ℕ) := certificate_1159_part_5_E

noncomputable def certificate_1159_part_7_E : List (ℕ × ℕ) := certificate_1159_part_6_E

noncomputable def certificate_1159_part_8_E : List (ℕ × ℕ) := certificate_1159_part_7_E

noncomputable def certificate_1159_part_9_E : List (ℕ × ℕ) := certificate_1159_part_8_E

noncomputable def certificate_1159_part_10_E : List (ℕ × ℕ) := certificate_1159_part_9_E

noncomputable def certificate_1159_part_11_E : List (ℕ × ℕ) := certificate_1159_part_10_E

noncomputable def certificate_1159_part_12_E : List (ℕ × ℕ) := certificate_1159_part_11_E

noncomputable def certificate_1159_part_15_E : List (ℕ × ℕ) := certificate_1159_part_12_E

noncomputable def certificate_1159_part_16_E : List (ℕ × ℕ) := certificate_1159_part_15_E

noncomputable def certificate_1159_part_17_E : List (ℕ × ℕ) := certificate_1159_part_16_E

noncomputable def certificate_1159_part_20_E : List (ℕ × ℕ) := certificate_1159_part_17_E

noncomputable def certificate_1159_part_21_E : List (ℕ × ℕ) := certificate_1159_part_20_E

noncomputable def certificate_1159_part_34_E : List (ℕ × ℕ) := certificate_1159_part_21_E

noncomputable def certificate_1159_part_38_E : List (ℕ × ℕ) := certificate_1159_part_34_E

noncomputable def certificate_1159_part_59_E : List (ℕ × ℕ) := certificate_1159_part_38_E

noncomputable def certificate_1159_part_79_E : List (ℕ × ℕ) := certificate_1159_part_59_E

noncomputable def certificate_1159_part_99_E : List (ℕ × ℕ) := certificate_1159_part_79_E

noncomputable def certificate_1159_part_110_E : List (ℕ × ℕ) := certificate_1159_part_99_E

noncomputable def certificate_1159_part_118_E : List (ℕ × ℕ) := certificate_1159_part_110_E

noncomputable def certificate_1159_part_128_E : List (ℕ × ℕ) := certificate_1159_part_118_E

noncomputable def certificate_1159_part_129_E : List (ℕ × ℕ) := certificate_1159_part_128_E

noncomputable def certificate_1159_part_130_E : List (ℕ × ℕ) := certificate_1159_part_129_E

noncomputable def certificate_1159_part_131_E : List (ℕ × ℕ) := certificate_1159_part_130_E

noncomputable def certificate_1159_part_132_E : List (ℕ × ℕ) := certificate_1159_part_131_E

noncomputable def certificate_1159_part_133_E : List (ℕ × ℕ) := certificate_1159_part_132_E

noncomputable def certificate_1160_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_1160_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_1161_q : Finset ℕ := ([0,1,2,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_1161_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(1,2),(1,3),(1,4),(1,6),(1,9),(2,3),(2,4),(2,6),(2,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_1162_q : Finset ℕ := ([0,1,2,3,4,6,10] : List ℕ).toFinset
noncomputable def certificate_1162_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(1,2),(1,3),(1,4),(1,6),(1,10),(2,3),(2,4),(2,6),(2,10),(3,4),(3,6),(3,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_1163_q : Finset ℕ := ([0,1,2,3,4,6,11] : List ℕ).toFinset
noncomputable def certificate_1163_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(1,2),(1,3),(1,4),(1,6),(1,11),(2,3),(2,4),(2,6),(2,11),(3,4),(3,6),(3,11),(4,6),(4,11),(6,11)]

noncomputable def certificate_1164_q : Finset ℕ := ([0,1,2,3,4,6,12] : List ℕ).toFinset
noncomputable def certificate_1164_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(1,2),(1,3),(1,4),(1,6),(1,12),(2,3),(2,4),(2,6),(2,12),(3,4),(3,6),(3,12),(4,6),(4,12),(6,12)]

noncomputable def certificate_1165_q : Finset ℕ := ([0,1,2,3,4,6,13] : List ℕ).toFinset
noncomputable def certificate_1165_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,13),(1,2),(1,3),(1,4),(1,6),(1,13),(2,3),(2,4),(2,6),(2,13),(3,4),(3,6),(3,13),(4,6),(4,13),(6,13)]

noncomputable def certificate_1166_q : Finset ℕ := ([0,1,2,3,4,6,14] : List ℕ).toFinset
noncomputable def certificate_1166_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,14),(1,2),(1,3),(1,4),(1,6),(1,14),(2,3),(2,4),(2,6),(2,14),(3,4),(3,6),(3,14),(4,6),(4,14),(6,14)]

noncomputable def certificate_1167_q : Finset ℕ := ([0,1,2,3,4,7,10] : List ℕ).toFinset
noncomputable def certificate_1167_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(1,2),(1,3),(1,4),(1,7),(1,10),(2,3),(2,4),(2,7),(2,10),(3,4),(3,7),(3,10),(4,7),(4,10),(7,10)]

noncomputable def certificate_1168_q : Finset ℕ := ([0,1,2,3,4,7,11] : List ℕ).toFinset
noncomputable def certificate_1168_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(1,2),(1,3),(1,4),(1,7),(1,11),(2,3),(2,4),(2,7),(2,11),(3,4),(3,7),(3,11),(4,7),(4,11),(7,11)]

noncomputable def certificate_1169_q : Finset ℕ := ([0,1,2,3,4,7,12] : List ℕ).toFinset
noncomputable def certificate_1169_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,12),(1,2),(1,3),(1,4),(1,7),(1,12),(2,3),(2,4),(2,7),(2,12),(3,4),(3,7),(3,12),(4,7),(4,12),(7,12)]

noncomputable def certificate_1170_q : Finset ℕ := ([0,1,2,3,4,7,13] : List ℕ).toFinset
noncomputable def certificate_1170_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,13),(1,2),(1,3),(1,4),(1,7),(1,13),(2,3),(2,4),(2,7),(2,13),(3,4),(3,7),(3,13),(4,7),(4,13),(7,13)]

noncomputable def certificate_1171_q : Finset ℕ := ([0,1,2,3,4,7,14] : List ℕ).toFinset
noncomputable def certificate_1171_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,14),(1,2),(1,3),(1,4),(1,7),(1,14),(2,3),(2,4),(2,7),(2,14),(3,4),(3,7),(3,14),(4,7),(4,14),(7,14)]

noncomputable def certificate_1172_q : Finset ℕ := ([0,1,2,3,4,8,12] : List ℕ).toFinset
noncomputable def certificate_1172_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,8),(0,12),(1,2),(1,3),(1,4),(1,8),(1,12),(2,3),(2,4),(2,8),(2,12),(3,4),(3,8),(3,12),(4,8),(4,12),(8,12)]

noncomputable def certificate_1173_q : Finset ℕ := ([0,1,2,3,4,8,13] : List ℕ).toFinset
noncomputable def certificate_1173_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,8),(0,13),(1,2),(1,3),(1,4),(1,8),(1,13),(2,3),(2,4),(2,8),(2,13),(3,4),(3,8),(3,13),(4,8),(4,13),(8,13)]

noncomputable def certificate_1174_q : Finset ℕ := ([0,1,2,3,4,8,14] : List ℕ).toFinset
noncomputable def certificate_1174_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,14),(1,2),(1,3),(1,4),(1,8),(1,14),(2,3),(2,4),(2,8),(2,14),(3,4),(3,8),(3,14),(4,8),(4,14),(8,14)]

noncomputable def certificate_1175_q : Finset ℕ := ([0,1,2,3,4,9,14] : List ℕ).toFinset

noncomputable def certificate_1175_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,9),(0,14),(1,2),(1,3),(1,4),(1,9),(1,14),(2,3),(2,4),(2,9),(2,14),(3,4),(3,9),(3,14),(4,9),(4,14),(9,14)]

noncomputable def certificate_1175_E : List (ℕ × ℕ) := certificate_1175_edges

noncomputable def certificate_1175_part_1_E : List (ℕ × ℕ) := certificate_1175_E

noncomputable def certificate_1175_part_2_E : List (ℕ × ℕ) := certificate_1175_part_1_E

noncomputable def certificate_1175_part_3_E : List (ℕ × ℕ) := certificate_1175_part_2_E

noncomputable def certificate_1175_part_4_E : List (ℕ × ℕ) := certificate_1175_part_3_E

noncomputable def certificate_1175_part_5_E : List (ℕ × ℕ) := certificate_1175_part_4_E

noncomputable def certificate_1175_part_6_E : List (ℕ × ℕ) := certificate_1175_part_5_E

noncomputable def certificate_1175_part_7_E : List (ℕ × ℕ) := certificate_1175_part_6_E

noncomputable def certificate_1175_part_8_E : List (ℕ × ℕ) := certificate_1175_part_7_E

noncomputable def certificate_1175_part_9_E : List (ℕ × ℕ) := certificate_1175_part_8_E

noncomputable def certificate_1175_part_10_E : List (ℕ × ℕ) := certificate_1175_part_9_E

noncomputable def certificate_1175_part_11_E : List (ℕ × ℕ) := certificate_1175_part_10_E

noncomputable def certificate_1175_part_21_E : List (ℕ × ℕ) := certificate_1175_part_11_E

noncomputable def certificate_1175_part_23_E : List (ℕ × ℕ) := certificate_1175_part_21_E

noncomputable def certificate_1175_part_30_E : List (ℕ × ℕ) := certificate_1175_part_23_E

noncomputable def certificate_1175_part_37_E : List (ℕ × ℕ) := certificate_1175_part_30_E

noncomputable def certificate_1175_part_40_E : List (ℕ × ℕ) := certificate_1175_part_37_E

noncomputable def certificate_1175_part_41_E : List (ℕ × ℕ) := certificate_1175_part_40_E

noncomputable def certificate_1175_part_43_E : List (ℕ × ℕ) := certificate_1175_part_41_E

noncomputable def certificate_1175_part_44_E : List (ℕ × ℕ) := certificate_1175_part_43_E

noncomputable def certificate_1175_part_45_E : List (ℕ × ℕ) := certificate_1175_part_44_E

noncomputable def certificate_1175_part_46_E : List (ℕ × ℕ) := certificate_1175_part_45_E

noncomputable def certificate_1175_part_52_E : List (ℕ × ℕ) := certificate_1175_part_46_E

noncomputable def certificate_1176_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_1176_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_1177_q : Finset ℕ := ([0,1,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_1177_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(1,2),(1,3),(1,5),(1,6),(1,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_1178_q : Finset ℕ := ([0,1,2,3,5,6,10] : List ℕ).toFinset
noncomputable def certificate_1178_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(1,2),(1,3),(1,5),(1,6),(1,10),(2,3),(2,5),(2,6),(2,10),(3,5),(3,6),(3,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_1179_q : Finset ℕ := ([0,1,2,3,5,6,11] : List ℕ).toFinset
noncomputable def certificate_1179_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,11),(1,2),(1,3),(1,5),(1,6),(1,11),(2,3),(2,5),(2,6),(2,11),(3,5),(3,6),(3,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_1180_q : Finset ℕ := ([0,1,2,3,5,6,12] : List ℕ).toFinset
noncomputable def certificate_1180_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,12),(1,2),(1,3),(1,5),(1,6),(1,12),(2,3),(2,5),(2,6),(2,12),(3,5),(3,6),(3,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_1181_q : Finset ℕ := ([0,1,2,3,5,6,13] : List ℕ).toFinset
noncomputable def certificate_1181_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,13),(1,2),(1,3),(1,5),(1,6),(1,13),(2,3),(2,5),(2,6),(2,13),(3,5),(3,6),(3,13),(5,6),(5,13),(6,13)]

noncomputable def certificate_1182_q : Finset ℕ := ([0,1,2,3,5,6,14] : List ℕ).toFinset
noncomputable def certificate_1182_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,14),(1,2),(1,3),(1,5),(1,6),(1,14),(2,3),(2,5),(2,6),(2,14),(3,5),(3,6),(3,14),(5,6),(5,14),(6,14)]

noncomputable def certificate_1183_q : Finset ℕ := ([0,1,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_1183_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(1,2),(1,3),(1,5),(1,7),(1,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

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

noncomputable def certificate_1184_q : Finset ℕ := ([0,1,2,3,5,7,10] : List ℕ).toFinset
noncomputable def certificate_1184_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(1,2),(1,3),(1,5),(1,7),(1,10),(2,3),(2,5),(2,7),(2,10),(3,5),(3,7),(3,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_1185_q : Finset ℕ := ([0,1,2,3,5,7,11] : List ℕ).toFinset
noncomputable def certificate_1185_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(1,2),(1,3),(1,5),(1,7),(1,11),(2,3),(2,5),(2,7),(2,11),(3,5),(3,7),(3,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_1186_q : Finset ℕ := ([0,1,2,3,5,7,12] : List ℕ).toFinset
noncomputable def certificate_1186_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(1,2),(1,3),(1,5),(1,7),(1,12),(2,3),(2,5),(2,7),(2,12),(3,5),(3,7),(3,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_1187_q : Finset ℕ := ([0,1,2,3,5,7,13] : List ℕ).toFinset
noncomputable def certificate_1187_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,13),(1,2),(1,3),(1,5),(1,7),(1,13),(2,3),(2,5),(2,7),(2,13),(3,5),(3,7),(3,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_1188_q : Finset ℕ := ([0,1,2,3,5,7,14] : List ℕ).toFinset
noncomputable def certificate_1188_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,14),(1,2),(1,3),(1,5),(1,7),(1,14),(2,3),(2,5),(2,7),(2,14),(3,5),(3,7),(3,14),(5,7),(5,14),(7,14)]

noncomputable def certificate_1189_q : Finset ℕ := ([0,1,2,3,5,8,10] : List ℕ).toFinset
noncomputable def certificate_1189_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(1,2),(1,3),(1,5),(1,8),(1,10),(2,3),(2,5),(2,8),(2,10),(3,5),(3,8),(3,10),(5,8),(5,10),(8,10)]

noncomputable def certificate_1190_q : Finset ℕ := ([0,1,2,3,5,8,11] : List ℕ).toFinset
noncomputable def certificate_1190_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(1,2),(1,3),(1,5),(1,8),(1,11),(2,3),(2,5),(2,8),(2,11),(3,5),(3,8),(3,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_1191_q : Finset ℕ := ([0,1,2,3,5,8,12] : List ℕ).toFinset
noncomputable def certificate_1191_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(1,2),(1,3),(1,5),(1,8),(1,12),(2,3),(2,5),(2,8),(2,12),(3,5),(3,8),(3,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_1192_q : Finset ℕ := ([0,1,2,3,5,8,13] : List ℕ).toFinset
noncomputable def certificate_1192_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,13),(1,2),(1,3),(1,5),(1,8),(1,13),(2,3),(2,5),(2,8),(2,13),(3,5),(3,8),(3,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_1193_q : Finset ℕ := ([0,1,2,3,5,8,14] : List ℕ).toFinset
noncomputable def certificate_1193_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,14),(1,2),(1,3),(1,5),(1,8),(1,14),(2,3),(2,5),(2,8),(2,14),(3,5),(3,8),(3,14),(5,8),(5,14),(8,14)]

noncomputable def certificate_1194_q : Finset ℕ := ([0,1,2,3,5,9,11] : List ℕ).toFinset
noncomputable def certificate_1194_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(1,2),(1,3),(1,5),(1,9),(1,11),(2,3),(2,5),(2,9),(2,11),(3,5),(3,9),(3,11),(5,9),(5,11),(9,11)]

noncomputable def certificate_1195_q : Finset ℕ := ([0,1,2,3,5,9,12] : List ℕ).toFinset
noncomputable def certificate_1195_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,9),(0,12),(1,2),(1,3),(1,5),(1,9),(1,12),(2,3),(2,5),(2,9),(2,12),(3,5),(3,9),(3,12),(5,9),(5,12),(9,12)]

noncomputable def certificate_1196_q : Finset ℕ := ([0,1,2,3,5,9,13] : List ℕ).toFinset
noncomputable def certificate_1196_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,9),(0,13),(1,2),(1,3),(1,5),(1,9),(1,13),(2,3),(2,5),(2,9),(2,13),(3,5),(3,9),(3,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_1197_q : Finset ℕ := ([0,1,2,3,5,9,14] : List ℕ).toFinset
noncomputable def certificate_1197_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,14),(1,2),(1,3),(1,5),(1,9),(1,14),(2,3),(2,5),(2,9),(2,14),(3,5),(3,9),(3,14),(5,9),(5,14),(9,14)]

noncomputable def certificate_1198_q : Finset ℕ := ([0,1,2,3,5,10,12] : List ℕ).toFinset
noncomputable def certificate_1198_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,10),(0,12),(1,2),(1,3),(1,5),(1,10),(1,12),(2,3),(2,5),(2,10),(2,12),(3,5),(3,10),(3,12),(5,10),(5,12),(10,12)]

noncomputable def certificate_1199_q : Finset ℕ := ([0,1,2,3,5,10,13] : List ℕ).toFinset
noncomputable def certificate_1199_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,10),(0,13),(1,2),(1,3),(1,5),(1,10),(1,13),(2,3),(2,5),(2,10),(2,13),(3,5),(3,10),(3,13),(5,10),(5,13),(10,13)]

noncomputable def certificate_1200_q : Finset ℕ := ([0,1,2,3,5,10,14] : List ℕ).toFinset
noncomputable def certificate_1200_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,10),(0,14),(1,2),(1,3),(1,5),(1,10),(1,14),(2,3),(2,5),(2,10),(2,14),(3,5),(3,10),(3,14),(5,10),(5,14),(10,14)]

noncomputable def certificate_1201_q : Finset ℕ := ([0,1,2,3,5,11,13] : List ℕ).toFinset
noncomputable def certificate_1201_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,11),(0,13),(1,2),(1,3),(1,5),(1,11),(1,13),(2,3),(2,5),(2,11),(2,13),(3,5),(3,11),(3,13),(5,11),(5,13),(11,13)]

noncomputable def certificate_1202_q : Finset ℕ := ([0,1,2,3,5,11,14] : List ℕ).toFinset
noncomputable def certificate_1202_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,11),(0,14),(1,2),(1,3),(1,5),(1,11),(1,14),(2,3),(2,5),(2,11),(2,14),(3,5),(3,11),(3,14),(5,11),(5,14),(11,14)]

noncomputable def certificate_1203_q : Finset ℕ := ([0,1,2,3,5,12,14] : List ℕ).toFinset
noncomputable def certificate_1203_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,12),(0,14),(1,2),(1,3),(1,5),(1,12),(1,14),(2,3),(2,5),(2,12),(2,14),(3,5),(3,12),(3,14),(5,12),(5,14),(12,14)]

noncomputable def certificate_1204_q : Finset ℕ := ([0,1,2,3,6,7,10] : List ℕ).toFinset
noncomputable def certificate_1204_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(1,2),(1,3),(1,6),(1,7),(1,10),(2,3),(2,6),(2,7),(2,10),(3,6),(3,7),(3,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_1205_q : Finset ℕ := ([0,1,2,3,6,7,11] : List ℕ).toFinset
noncomputable def certificate_1205_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(1,2),(1,3),(1,6),(1,7),(1,11),(2,3),(2,6),(2,7),(2,11),(3,6),(3,7),(3,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_1206_q : Finset ℕ := ([0,1,2,3,6,7,12] : List ℕ).toFinset
noncomputable def certificate_1206_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,7),(0,12),(1,2),(1,3),(1,6),(1,7),(1,12),(2,3),(2,6),(2,7),(2,12),(3,6),(3,7),(3,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_1207_q : Finset ℕ := ([0,1,2,3,6,7,13] : List ℕ).toFinset
noncomputable def certificate_1207_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,7),(0,13),(1,2),(1,3),(1,6),(1,7),(1,13),(2,3),(2,6),(2,7),(2,13),(3,6),(3,7),(3,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_1208_q : Finset ℕ := ([0,1,2,3,6,7,14] : List ℕ).toFinset
noncomputable def certificate_1208_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,7),(0,14),(1,2),(1,3),(1,6),(1,7),(1,14),(2,3),(2,6),(2,7),(2,14),(3,6),(3,7),(3,14),(6,7),(6,14),(7,14)]

noncomputable def certificate_1209_q : Finset ℕ := ([0,1,2,3,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1209_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(1,2),(1,3),(1,6),(1,8),(1,11),(2,3),(2,6),(2,8),(2,11),(3,6),(3,8),(3,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1210_q : Finset ℕ := ([0,1,2,3,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1210_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(1,2),(1,3),(1,6),(1,8),(1,12),(2,3),(2,6),(2,8),(2,12),(3,6),(3,8),(3,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1211_q : Finset ℕ := ([0,1,2,3,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1211_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,8),(0,13),(1,2),(1,3),(1,6),(1,8),(1,13),(2,3),(2,6),(2,8),(2,13),(3,6),(3,8),(3,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1212_q : Finset ℕ := ([0,1,2,3,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1212_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,14),(1,2),(1,3),(1,6),(1,8),(1,14),(2,3),(2,6),(2,8),(2,14),(3,6),(3,8),(3,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1213_q : Finset ℕ := ([0,1,2,3,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1213_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,6),(0,9),(0,12),(1,2),(1,3),(1,6),(1,9),(1,12),(2,3),(2,6),(2,9),(2,12),(3,6),(3,9),(3,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1214_q : Finset ℕ := ([0,1,2,3,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1214_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,9),(0,13),(1,2),(1,3),(1,6),(1,9),(1,13),(2,3),(2,6),(2,9),(2,13),(3,6),(3,9),(3,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1215_q : Finset ℕ := ([0,1,2,3,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1215_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,9),(0,14),(1,2),(1,3),(1,6),(1,9),(1,14),(2,3),(2,6),(2,9),(2,14),(3,6),(3,9),(3,14),(6,9),(6,14),(9,14)]

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

noncomputable def certificate_1216_q : Finset ℕ := ([0,1,2,3,6,10,13] : List ℕ).toFinset
noncomputable def certificate_1216_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,10),(0,13),(1,2),(1,3),(1,6),(1,10),(1,13),(2,3),(2,6),(2,10),(2,13),(3,6),(3,10),(3,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_1217_q : Finset ℕ := ([0,1,2,3,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1217_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,10),(0,14),(1,2),(1,3),(1,6),(1,10),(1,14),(2,3),(2,6),(2,10),(2,14),(3,6),(3,10),(3,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1218_q : Finset ℕ := ([0,1,2,3,6,11,14] : List ℕ).toFinset
noncomputable def certificate_1218_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,11),(0,14),(1,2),(1,3),(1,6),(1,11),(1,14),(2,3),(2,6),(2,11),(2,14),(3,6),(3,11),(3,14),(6,11),(6,14),(11,14)]

noncomputable def certificate_1219_q : Finset ℕ := ([0,1,2,3,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1219_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,7),(0,8),(0,12),(1,2),(1,3),(1,7),(1,8),(1,12),(2,3),(2,7),(2,8),(2,12),(3,7),(3,8),(3,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1220_q : Finset ℕ := ([0,1,2,3,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1220_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,7),(0,8),(0,13),(1,2),(1,3),(1,7),(1,8),(1,13),(2,3),(2,7),(2,8),(2,13),(3,7),(3,8),(3,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1221_q : Finset ℕ := ([0,1,2,3,7,8,14] : List ℕ).toFinset

noncomputable def certificate_1221_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,7),(0,8),(0,14),(1,2),(1,3),(1,7),(1,8),(1,14),(2,3),(2,7),(2,8),(2,14),(3,7),(3,8),(3,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1221_E : List (ℕ × ℕ) := certificate_1221_edges

noncomputable def certificate_1221_part_1_E : List (ℕ × ℕ) := certificate_1221_E

noncomputable def certificate_1221_part_2_E : List (ℕ × ℕ) := certificate_1221_part_1_E

noncomputable def certificate_1221_part_3_E : List (ℕ × ℕ) := certificate_1221_part_2_E

noncomputable def certificate_1221_part_4_E : List (ℕ × ℕ) := certificate_1221_part_3_E

noncomputable def certificate_1221_part_5_E : List (ℕ × ℕ) := certificate_1221_part_4_E

noncomputable def certificate_1221_part_6_E : List (ℕ × ℕ) := certificate_1221_part_5_E

noncomputable def certificate_1221_part_7_E : List (ℕ × ℕ) := certificate_1221_part_6_E

noncomputable def certificate_1221_part_8_E : List (ℕ × ℕ) := certificate_1221_part_7_E

noncomputable def certificate_1221_part_9_E : List (ℕ × ℕ) := certificate_1221_part_8_E

noncomputable def certificate_1221_part_10_E : List (ℕ × ℕ) := certificate_1221_part_9_E

noncomputable def certificate_1221_part_11_E : List (ℕ × ℕ) := certificate_1221_part_10_E

noncomputable def certificate_1221_part_13_E : List (ℕ × ℕ) := certificate_1221_part_11_E

noncomputable def certificate_1221_part_14_E : List (ℕ × ℕ) := certificate_1221_part_13_E

noncomputable def certificate_1221_part_15_E : List (ℕ × ℕ) := certificate_1221_part_14_E

noncomputable def certificate_1221_part_16_E : List (ℕ × ℕ) := certificate_1221_part_15_E

noncomputable def certificate_1221_part_18_E : List (ℕ × ℕ) := certificate_1221_part_16_E

noncomputable def certificate_1221_part_19_E : List (ℕ × ℕ) := certificate_1221_part_18_E

noncomputable def certificate_1221_part_20_E : List (ℕ × ℕ) := certificate_1221_part_19_E

noncomputable def certificate_1221_part_24_E : List (ℕ × ℕ) := certificate_1221_part_20_E

noncomputable def certificate_1221_part_26_E : List (ℕ × ℕ) := certificate_1221_part_24_E

noncomputable def certificate_1221_part_27_E : List (ℕ × ℕ) := certificate_1221_part_26_E

noncomputable def certificate_1221_part_28_E : List (ℕ × ℕ) := certificate_1221_part_27_E

noncomputable def certificate_1221_part_29_E : List (ℕ × ℕ) := certificate_1221_part_28_E

noncomputable def certificate_1221_part_30_E : List (ℕ × ℕ) := certificate_1221_part_29_E

noncomputable def certificate_1221_part_31_E : List (ℕ × ℕ) := certificate_1221_part_30_E

noncomputable def certificate_1221_part_32_E : List (ℕ × ℕ) := certificate_1221_part_31_E

noncomputable def certificate_1221_part_37_E : List (ℕ × ℕ) := certificate_1221_part_32_E

noncomputable def certificate_1221_part_41_E : List (ℕ × ℕ) := certificate_1221_part_37_E

noncomputable def certificate_1221_part_42_E : List (ℕ × ℕ) := certificate_1221_part_41_E

noncomputable def certificate_1221_part_49_E : List (ℕ × ℕ) := certificate_1221_part_42_E

noncomputable def certificate_1221_part_55_E : List (ℕ × ℕ) := certificate_1221_part_49_E

noncomputable def certificate_1221_part_58_E : List (ℕ × ℕ) := certificate_1221_part_55_E

noncomputable def certificate_1222_q : Finset ℕ := ([0,1,2,3,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1222_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,7),(0,9),(0,13),(1,2),(1,3),(1,7),(1,9),(1,13),(2,3),(2,7),(2,9),(2,13),(3,7),(3,9),(3,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1223_q : Finset ℕ := ([0,1,2,3,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1223_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,7),(0,9),(0,14),(1,2),(1,3),(1,7),(1,9),(1,14),(2,3),(2,7),(2,9),(2,14),(3,7),(3,9),(3,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1224_q : Finset ℕ := ([0,1,2,3,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1224_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,7),(0,10),(0,14),(1,2),(1,3),(1,7),(1,10),(1,14),(2,3),(2,7),(2,10),(2,14),(3,7),(3,10),(3,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1225_q : Finset ℕ := ([0,1,2,3,8,9,14] : List ℕ).toFinset

noncomputable def certificate_1225_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,8),(0,9),(0,14),(1,2),(1,3),(1,8),(1,9),(1,14),(2,3),(2,8),(2,9),(2,14),(3,8),(3,9),(3,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1225_E : List (ℕ × ℕ) := certificate_1225_edges

noncomputable def certificate_1225_part_1_E : List (ℕ × ℕ) := certificate_1225_E

noncomputable def certificate_1225_part_2_E : List (ℕ × ℕ) := certificate_1225_part_1_E

noncomputable def certificate_1225_part_3_E : List (ℕ × ℕ) := certificate_1225_part_2_E

noncomputable def certificate_1225_part_4_E : List (ℕ × ℕ) := certificate_1225_part_3_E

noncomputable def certificate_1225_part_5_E : List (ℕ × ℕ) := certificate_1225_part_4_E

noncomputable def certificate_1225_part_6_E : List (ℕ × ℕ) := certificate_1225_part_5_E

noncomputable def certificate_1225_part_7_E : List (ℕ × ℕ) := certificate_1225_part_6_E

noncomputable def certificate_1225_part_8_E : List (ℕ × ℕ) := certificate_1225_part_7_E

noncomputable def certificate_1225_part_9_E : List (ℕ × ℕ) := certificate_1225_part_8_E

noncomputable def certificate_1225_part_10_E : List (ℕ × ℕ) := certificate_1225_part_9_E

noncomputable def certificate_1225_part_11_E : List (ℕ × ℕ) := certificate_1225_part_10_E

noncomputable def certificate_1225_part_13_E : List (ℕ × ℕ) := certificate_1225_part_11_E

noncomputable def certificate_1225_part_14_E : List (ℕ × ℕ) := certificate_1225_part_13_E

noncomputable def certificate_1225_part_15_E : List (ℕ × ℕ) := certificate_1225_part_14_E

noncomputable def certificate_1225_part_16_E : List (ℕ × ℕ) := certificate_1225_part_15_E

noncomputable def certificate_1225_part_17_E : List (ℕ × ℕ) := certificate_1225_part_16_E

noncomputable def certificate_1225_part_18_E : List (ℕ × ℕ) := certificate_1225_part_17_E

noncomputable def certificate_1225_part_19_E : List (ℕ × ℕ) := certificate_1225_part_18_E

noncomputable def certificate_1225_part_20_E : List (ℕ × ℕ) := certificate_1225_part_19_E

noncomputable def certificate_1225_part_23_E : List (ℕ × ℕ) := certificate_1225_part_20_E

noncomputable def certificate_1225_part_24_E : List (ℕ × ℕ) := certificate_1225_part_23_E

noncomputable def certificate_1225_part_25_E : List (ℕ × ℕ) := certificate_1225_part_24_E

noncomputable def certificate_1225_part_26_E : List (ℕ × ℕ) := certificate_1225_part_25_E

noncomputable def certificate_1225_part_30_E : List (ℕ × ℕ) := certificate_1225_part_26_E

noncomputable def certificate_1225_part_36_E : List (ℕ × ℕ) := certificate_1225_part_30_E

noncomputable def certificate_1225_part_37_E : List (ℕ × ℕ) := certificate_1225_part_36_E

noncomputable def certificate_1225_part_39_E : List (ℕ × ℕ) := certificate_1225_part_37_E

noncomputable def certificate_1225_part_40_E : List (ℕ × ℕ) := certificate_1225_part_39_E

noncomputable def certificate_1225_part_41_E : List (ℕ × ℕ) := certificate_1225_part_40_E

noncomputable def certificate_1225_part_43_E : List (ℕ × ℕ) := certificate_1225_part_41_E

noncomputable def certificate_1225_part_46_E : List (ℕ × ℕ) := certificate_1225_part_43_E

noncomputable def certificate_1225_part_47_E : List (ℕ × ℕ) := certificate_1225_part_46_E

noncomputable def certificate_1225_part_48_E : List (ℕ × ℕ) := certificate_1225_part_47_E

noncomputable def certificate_1225_part_59_E : List (ℕ × ℕ) := certificate_1225_part_48_E

noncomputable def certificate_1225_part_60_E : List (ℕ × ℕ) := certificate_1225_part_59_E

noncomputable def certificate_1225_part_66_E : List (ℕ × ℕ) := certificate_1225_part_60_E

noncomputable def certificate_1225_part_75_E : List (ℕ × ℕ) := certificate_1225_part_66_E

noncomputable def certificate_1225_part_77_E : List (ℕ × ℕ) := certificate_1225_part_75_E

noncomputable def certificate_1225_part_78_E : List (ℕ × ℕ) := certificate_1225_part_77_E

noncomputable def certificate_1225_part_90_E : List (ℕ × ℕ) := certificate_1225_part_78_E

noncomputable def certificate_1225_part_99_E : List (ℕ × ℕ) := certificate_1225_part_90_E

noncomputable def certificate_1225_part_100_E : List (ℕ × ℕ) := certificate_1225_part_99_E

noncomputable def certificate_1225_part_107_E : List (ℕ × ℕ) := certificate_1225_part_100_E

noncomputable def certificate_1225_part_108_E : List (ℕ × ℕ) := certificate_1225_part_107_E

noncomputable def certificate_1225_part_115_E : List (ℕ × ℕ) := certificate_1225_part_108_E

noncomputable def certificate_1226_q : Finset ℕ := ([0,1,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_1226_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(1,2),(1,4),(1,5),(1,7),(1,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_1227_q : Finset ℕ := ([0,1,2,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_1227_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(1,2),(1,4),(1,5),(1,7),(1,10),(2,4),(2,5),(2,7),(2,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_1228_q : Finset ℕ := ([0,1,2,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_1228_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(1,2),(1,4),(1,5),(1,7),(1,11),(2,4),(2,5),(2,7),(2,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_1229_q : Finset ℕ := ([0,1,2,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_1229_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(1,2),(1,4),(1,5),(1,7),(1,12),(2,4),(2,5),(2,7),(2,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_1230_q : Finset ℕ := ([0,1,2,4,5,7,13] : List ℕ).toFinset
noncomputable def certificate_1230_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,13),(1,2),(1,4),(1,5),(1,7),(1,13),(2,4),(2,5),(2,7),(2,13),(4,5),(4,7),(4,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_1231_q : Finset ℕ := ([0,1,2,4,5,7,14] : List ℕ).toFinset
noncomputable def certificate_1231_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,14),(1,2),(1,4),(1,5),(1,7),(1,14),(2,4),(2,5),(2,7),(2,14),(4,5),(4,7),(4,14),(5,7),(5,14),(7,14)]

noncomputable def certificate_1232_q : Finset ℕ := ([0,1,2,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_1232_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(1,2),(1,4),(1,5),(1,8),(1,11),(2,4),(2,5),(2,8),(2,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_1233_q : Finset ℕ := ([0,1,2,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_1233_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,12),(1,2),(1,4),(1,5),(1,8),(1,12),(2,4),(2,5),(2,8),(2,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_1234_q : Finset ℕ := ([0,1,2,4,5,8,13] : List ℕ).toFinset
noncomputable def certificate_1234_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,13),(1,2),(1,4),(1,5),(1,8),(1,13),(2,4),(2,5),(2,8),(2,13),(4,5),(4,8),(4,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_1235_q : Finset ℕ := ([0,1,2,4,5,8,14] : List ℕ).toFinset
noncomputable def certificate_1235_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,14),(1,2),(1,4),(1,5),(1,8),(1,14),(2,4),(2,5),(2,8),(2,14),(4,5),(4,8),(4,14),(5,8),(5,14),(8,14)]

noncomputable def certificate_1236_q : Finset ℕ := ([0,1,2,4,5,9,13] : List ℕ).toFinset
noncomputable def certificate_1236_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,9),(0,13),(1,2),(1,4),(1,5),(1,9),(1,13),(2,4),(2,5),(2,9),(2,13),(4,5),(4,9),(4,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_1237_q : Finset ℕ := ([0,1,2,4,5,9,14] : List ℕ).toFinset
noncomputable def certificate_1237_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,9),(0,14),(1,2),(1,4),(1,5),(1,9),(1,14),(2,4),(2,5),(2,9),(2,14),(4,5),(4,9),(4,14),(5,9),(5,14),(9,14)]

noncomputable def certificate_1238_q : Finset ℕ := ([0,1,2,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_1238_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(1,2),(1,4),(1,6),(1,7),(1,10),(2,4),(2,6),(2,7),(2,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_1239_q : Finset ℕ := ([0,1,2,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_1239_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(1,2),(1,4),(1,6),(1,7),(1,11),(2,4),(2,6),(2,7),(2,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_1240_q : Finset ℕ := ([0,1,2,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_1240_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,12),(1,2),(1,4),(1,6),(1,7),(1,12),(2,4),(2,6),(2,7),(2,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_1241_q : Finset ℕ := ([0,1,2,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_1241_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,13),(1,2),(1,4),(1,6),(1,7),(1,13),(2,4),(2,6),(2,7),(2,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_1242_q : Finset ℕ := ([0,1,2,4,6,7,14] : List ℕ).toFinset
noncomputable def certificate_1242_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,14),(1,2),(1,4),(1,6),(1,7),(1,14),(2,4),(2,6),(2,7),(2,14),(4,6),(4,7),(4,14),(6,7),(6,14),(7,14)]

noncomputable def certificate_1243_q : Finset ℕ := ([0,1,2,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1243_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(1,2),(1,4),(1,6),(1,8),(1,10),(2,4),(2,6),(2,8),(2,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1244_q : Finset ℕ := ([0,1,2,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1244_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(1,2),(1,4),(1,6),(1,8),(1,11),(2,4),(2,6),(2,8),(2,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1245_q : Finset ℕ := ([0,1,2,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1245_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(1,2),(1,4),(1,6),(1,8),(1,12),(2,4),(2,6),(2,8),(2,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1246_q : Finset ℕ := ([0,1,2,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1246_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,13),(1,2),(1,4),(1,6),(1,8),(1,13),(2,4),(2,6),(2,8),(2,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1247_q : Finset ℕ := ([0,1,2,4,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1247_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,14),(1,2),(1,4),(1,6),(1,8),(1,14),(2,4),(2,6),(2,8),(2,14),(4,6),(4,8),(4,14),(6,8),(6,14),(8,14)]

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

noncomputable def certificate_1248_q : Finset ℕ := ([0,1,2,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_1248_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(1,2),(1,4),(1,6),(1,9),(1,11),(2,4),(2,6),(2,9),(2,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_1249_q : Finset ℕ := ([0,1,2,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1249_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(1,2),(1,4),(1,6),(1,9),(1,12),(2,4),(2,6),(2,9),(2,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1250_q : Finset ℕ := ([0,1,2,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1250_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,13),(1,2),(1,4),(1,6),(1,9),(1,13),(2,4),(2,6),(2,9),(2,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1251_q : Finset ℕ := ([0,1,2,4,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1251_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,14),(1,2),(1,4),(1,6),(1,9),(1,14),(2,4),(2,6),(2,9),(2,14),(4,6),(4,9),(4,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1252_q : Finset ℕ := ([0,1,2,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_1252_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(1,2),(1,4),(1,6),(1,10),(1,12),(2,4),(2,6),(2,10),(2,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_1253_q : Finset ℕ := ([0,1,2,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_1253_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,10),(0,13),(1,2),(1,4),(1,6),(1,10),(1,13),(2,4),(2,6),(2,10),(2,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_1254_q : Finset ℕ := ([0,1,2,4,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1254_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,14),(1,2),(1,4),(1,6),(1,10),(1,14),(2,4),(2,6),(2,10),(2,14),(4,6),(4,10),(4,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1255_q : Finset ℕ := ([0,1,2,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_1255_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,11),(0,13),(1,2),(1,4),(1,6),(1,11),(1,13),(2,4),(2,6),(2,11),(2,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_1256_q : Finset ℕ := ([0,1,2,4,6,11,14] : List ℕ).toFinset
noncomputable def certificate_1256_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,11),(0,14),(1,2),(1,4),(1,6),(1,11),(1,14),(2,4),(2,6),(2,11),(2,14),(4,6),(4,11),(4,14),(6,11),(6,14),(11,14)]

noncomputable def certificate_1257_q : Finset ℕ := ([0,1,2,4,6,12,14] : List ℕ).toFinset
noncomputable def certificate_1257_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,12),(0,14),(1,2),(1,4),(1,6),(1,12),(1,14),(2,4),(2,6),(2,12),(2,14),(4,6),(4,12),(4,14),(6,12),(6,14),(12,14)]

noncomputable def certificate_1258_q : Finset ℕ := ([0,1,2,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1258_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(1,2),(1,4),(1,7),(1,8),(1,11),(2,4),(2,7),(2,8),(2,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1259_q : Finset ℕ := ([0,1,2,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1259_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,8),(0,12),(1,2),(1,4),(1,7),(1,8),(1,12),(2,4),(2,7),(2,8),(2,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1260_q : Finset ℕ := ([0,1,2,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1260_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,8),(0,13),(1,2),(1,4),(1,7),(1,8),(1,13),(2,4),(2,7),(2,8),(2,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1261_q : Finset ℕ := ([0,1,2,4,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1261_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,14),(1,2),(1,4),(1,7),(1,8),(1,14),(2,4),(2,7),(2,8),(2,14),(4,7),(4,8),(4,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1262_q : Finset ℕ := ([0,1,2,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1262_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(1,2),(1,4),(1,7),(1,9),(1,12),(2,4),(2,7),(2,9),(2,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1263_q : Finset ℕ := ([0,1,2,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1263_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,9),(0,13),(1,2),(1,4),(1,7),(1,9),(1,13),(2,4),(2,7),(2,9),(2,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1264_q : Finset ℕ := ([0,1,2,4,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1264_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,14),(1,2),(1,4),(1,7),(1,9),(1,14),(2,4),(2,7),(2,9),(2,14),(4,7),(4,9),(4,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1265_q : Finset ℕ := ([0,1,2,4,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1265_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,7),(0,10),(0,12),(1,2),(1,4),(1,7),(1,10),(1,12),(2,4),(2,7),(2,10),(2,12),(4,7),(4,10),(4,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1266_q : Finset ℕ := ([0,1,2,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1266_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,10),(0,13),(1,2),(1,4),(1,7),(1,10),(1,13),(2,4),(2,7),(2,10),(2,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1267_q : Finset ℕ := ([0,1,2,4,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1267_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,10),(0,14),(1,2),(1,4),(1,7),(1,10),(1,14),(2,4),(2,7),(2,10),(2,14),(4,7),(4,10),(4,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1268_q : Finset ℕ := ([0,1,2,4,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1268_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,11),(0,13),(1,2),(1,4),(1,7),(1,11),(1,13),(2,4),(2,7),(2,11),(2,13),(4,7),(4,11),(4,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1269_q : Finset ℕ := ([0,1,2,4,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1269_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,11),(0,14),(1,2),(1,4),(1,7),(1,11),(1,14),(2,4),(2,7),(2,11),(2,14),(4,7),(4,11),(4,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1270_q : Finset ℕ := ([0,1,2,4,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1270_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,12),(0,14),(1,2),(1,4),(1,7),(1,12),(1,14),(2,4),(2,7),(2,12),(2,14),(4,7),(4,12),(4,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1271_q : Finset ℕ := ([0,1,2,4,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1271_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,8),(0,9),(0,12),(1,2),(1,4),(1,8),(1,9),(1,12),(2,4),(2,8),(2,9),(2,12),(4,8),(4,9),(4,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1272_q : Finset ℕ := ([0,1,2,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1272_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,8),(0,9),(0,13),(1,2),(1,4),(1,8),(1,9),(1,13),(2,4),(2,8),(2,9),(2,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1273_q : Finset ℕ := ([0,1,2,4,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1273_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,9),(0,14),(1,2),(1,4),(1,8),(1,9),(1,14),(2,4),(2,8),(2,9),(2,14),(4,8),(4,9),(4,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1274_q : Finset ℕ := ([0,1,2,4,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1274_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,8),(0,10),(0,13),(1,2),(1,4),(1,8),(1,10),(1,13),(2,4),(2,8),(2,10),(2,13),(4,8),(4,10),(4,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1275_q : Finset ℕ := ([0,1,2,4,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1275_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,10),(0,14),(1,2),(1,4),(1,8),(1,10),(1,14),(2,4),(2,8),(2,10),(2,14),(4,8),(4,10),(4,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1276_q : Finset ℕ := ([0,1,2,4,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1276_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,11),(0,14),(1,2),(1,4),(1,8),(1,11),(1,14),(2,4),(2,8),(2,11),(2,14),(4,8),(4,11),(4,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1277_q : Finset ℕ := ([0,1,2,4,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1277_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,12),(0,14),(1,2),(1,4),(1,8),(1,12),(1,14),(2,4),(2,8),(2,12),(2,14),(4,8),(4,12),(4,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1278_q : Finset ℕ := ([0,1,2,4,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1278_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,9),(0,10),(0,13),(1,2),(1,4),(1,9),(1,10),(1,13),(2,4),(2,9),(2,10),(2,13),(4,9),(4,10),(4,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1279_q : Finset ℕ := ([0,1,2,4,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1279_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,9),(0,10),(0,14),(1,2),(1,4),(1,9),(1,10),(1,14),(2,4),(2,9),(2,10),(2,14),(4,9),(4,10),(4,14),(9,10),(9,14),(10,14)]

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

noncomputable def certificate_1280_q : Finset ℕ := ([0,1,2,4,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1280_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,9),(0,11),(0,14),(1,2),(1,4),(1,9),(1,11),(1,14),(2,4),(2,9),(2,11),(2,14),(4,9),(4,11),(4,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1281_q : Finset ℕ := ([0,1,2,4,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1281_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,10),(0,11),(0,14),(1,2),(1,4),(1,10),(1,11),(1,14),(2,4),(2,10),(2,11),(2,14),(4,10),(4,11),(4,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1282_q : Finset ℕ := ([0,1,2,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1282_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,6),(0,9),(0,12),(1,2),(1,5),(1,6),(1,9),(1,12),(2,5),(2,6),(2,9),(2,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1283_q : Finset ℕ := ([0,1,2,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1283_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,6),(0,9),(0,13),(1,2),(1,5),(1,6),(1,9),(1,13),(2,5),(2,6),(2,9),(2,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1284_q : Finset ℕ := ([0,1,2,5,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1284_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,14),(1,2),(1,5),(1,6),(1,9),(1,14),(2,5),(2,6),(2,9),(2,14),(5,6),(5,9),(5,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1285_q : Finset ℕ := ([0,1,2,5,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1285_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,10),(0,14),(1,2),(1,5),(1,6),(1,10),(1,14),(2,5),(2,6),(2,10),(2,14),(5,6),(5,10),(5,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1286_q : Finset ℕ := ([0,1,2,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1286_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,5),(0,7),(0,9),(0,12),(1,2),(1,5),(1,7),(1,9),(1,12),(2,5),(2,7),(2,9),(2,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1287_q : Finset ℕ := ([0,1,2,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1287_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,7),(0,9),(0,13),(1,2),(1,5),(1,7),(1,9),(1,13),(2,5),(2,7),(2,9),(2,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1288_q : Finset ℕ := ([0,1,2,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1288_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,7),(0,9),(0,14),(1,2),(1,5),(1,7),(1,9),(1,14),(2,5),(2,7),(2,9),(2,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1289_q : Finset ℕ := ([0,1,2,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1289_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,7),(0,10),(0,13),(1,2),(1,5),(1,7),(1,10),(1,13),(2,5),(2,7),(2,10),(2,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1290_q : Finset ℕ := ([0,1,2,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1290_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,7),(0,10),(0,14),(1,2),(1,5),(1,7),(1,10),(1,14),(2,5),(2,7),(2,10),(2,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1291_q : Finset ℕ := ([0,1,2,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1291_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,7),(0,11),(0,14),(1,2),(1,5),(1,7),(1,11),(1,14),(2,5),(2,7),(2,11),(2,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1292_q : Finset ℕ := ([0,1,2,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1292_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,8),(0,9),(0,13),(1,2),(1,5),(1,8),(1,9),(1,13),(2,5),(2,8),(2,9),(2,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1293_q : Finset ℕ := ([0,1,2,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1293_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,8),(0,9),(0,14),(1,2),(1,5),(1,8),(1,9),(1,14),(2,5),(2,8),(2,9),(2,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1294_q : Finset ℕ := ([0,1,2,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1294_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,8),(0,10),(0,14),(1,2),(1,5),(1,8),(1,10),(1,14),(2,5),(2,8),(2,10),(2,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1295_q : Finset ℕ := ([0,1,2,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1295_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,8),(0,11),(0,14),(1,2),(1,5),(1,8),(1,11),(1,14),(2,5),(2,8),(2,11),(2,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1296_q : Finset ℕ := ([0,1,2,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1296_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,9),(0,10),(0,14),(1,2),(1,5),(1,9),(1,10),(1,14),(2,5),(2,9),(2,10),(2,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1297_q : Finset ℕ := ([0,1,2,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1297_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,6),(0,8),(0,10),(0,14),(1,2),(1,6),(1,8),(1,10),(1,14),(2,6),(2,8),(2,10),(2,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1298_q : Finset ℕ := ([0,1,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_1298_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(1,3),(1,4),(1,6),(1,7),(1,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_1299_q : Finset ℕ := ([0,1,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_1299_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(1,3),(1,4),(1,6),(1,7),(1,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_1300_q : Finset ℕ := ([0,1,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_1300_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(1,3),(1,4),(1,6),(1,7),(1,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_1301_q : Finset ℕ := ([0,1,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_1301_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,12),(1,3),(1,4),(1,6),(1,7),(1,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_1302_q : Finset ℕ := ([0,1,3,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_1302_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,13),(1,3),(1,4),(1,6),(1,7),(1,13),(3,4),(3,6),(3,7),(3,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_1303_q : Finset ℕ := ([0,1,3,4,6,7,14] : List ℕ).toFinset
noncomputable def certificate_1303_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,14),(1,3),(1,4),(1,6),(1,7),(1,14),(3,4),(3,6),(3,7),(3,14),(4,6),(4,7),(4,14),(6,7),(6,14),(7,14)]

noncomputable def certificate_1304_q : Finset ℕ := ([0,1,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1304_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(1,3),(1,4),(1,6),(1,8),(1,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1305_q : Finset ℕ := ([0,1,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1305_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(1,3),(1,4),(1,6),(1,8),(1,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1306_q : Finset ℕ := ([0,1,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1306_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(1,3),(1,4),(1,6),(1,8),(1,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1307_q : Finset ℕ := ([0,1,3,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1307_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,13),(1,3),(1,4),(1,6),(1,8),(1,13),(3,4),(3,6),(3,8),(3,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1308_q : Finset ℕ := ([0,1,3,4,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1308_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,14),(1,3),(1,4),(1,6),(1,8),(1,14),(3,4),(3,6),(3,8),(3,14),(4,6),(4,8),(4,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1309_q : Finset ℕ := ([0,1,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_1309_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(1,3),(1,4),(1,6),(1,9),(1,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_1310_q : Finset ℕ := ([0,1,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1310_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(1,3),(1,4),(1,6),(1,9),(1,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1311_q : Finset ℕ := ([0,1,3,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1311_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,9),(0,13),(1,3),(1,4),(1,6),(1,9),(1,13),(3,4),(3,6),(3,9),(3,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

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

noncomputable def certificate_1312_q : Finset ℕ := ([0,1,3,4,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1312_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,14),(1,3),(1,4),(1,6),(1,9),(1,14),(3,4),(3,6),(3,9),(3,14),(4,6),(4,9),(4,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1313_q : Finset ℕ := ([0,1,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_1313_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,10),(0,12),(1,3),(1,4),(1,6),(1,10),(1,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_1314_q : Finset ℕ := ([0,1,3,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_1314_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,10),(0,13),(1,3),(1,4),(1,6),(1,10),(1,13),(3,4),(3,6),(3,10),(3,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_1315_q : Finset ℕ := ([0,1,3,4,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1315_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,10),(0,14),(1,3),(1,4),(1,6),(1,10),(1,14),(3,4),(3,6),(3,10),(3,14),(4,6),(4,10),(4,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1316_q : Finset ℕ := ([0,1,3,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_1316_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,11),(0,13),(1,3),(1,4),(1,6),(1,11),(1,13),(3,4),(3,6),(3,11),(3,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_1317_q : Finset ℕ := ([0,1,3,4,6,11,14] : List ℕ).toFinset
noncomputable def certificate_1317_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,11),(0,14),(1,3),(1,4),(1,6),(1,11),(1,14),(3,4),(3,6),(3,11),(3,14),(4,6),(4,11),(4,14),(6,11),(6,14),(11,14)]

noncomputable def certificate_1318_q : Finset ℕ := ([0,1,3,4,6,12,14] : List ℕ).toFinset
noncomputable def certificate_1318_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,12),(0,14),(1,3),(1,4),(1,6),(1,12),(1,14),(3,4),(3,6),(3,12),(3,14),(4,6),(4,12),(4,14),(6,12),(6,14),(12,14)]

noncomputable def certificate_1319_q : Finset ℕ := ([0,1,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1319_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(1,3),(1,4),(1,7),(1,8),(1,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1320_q : Finset ℕ := ([0,1,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1320_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,8),(0,12),(1,3),(1,4),(1,7),(1,8),(1,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1321_q : Finset ℕ := ([0,1,3,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1321_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,7),(0,8),(0,13),(1,3),(1,4),(1,7),(1,8),(1,13),(3,4),(3,7),(3,8),(3,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1322_q : Finset ℕ := ([0,1,3,4,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1322_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,8),(0,14),(1,3),(1,4),(1,7),(1,8),(1,14),(3,4),(3,7),(3,8),(3,14),(4,7),(4,8),(4,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1323_q : Finset ℕ := ([0,1,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1323_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,7),(0,9),(0,12),(1,3),(1,4),(1,7),(1,9),(1,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1324_q : Finset ℕ := ([0,1,3,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1324_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,7),(0,9),(0,13),(1,3),(1,4),(1,7),(1,9),(1,13),(3,4),(3,7),(3,9),(3,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1325_q : Finset ℕ := ([0,1,3,4,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1325_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,9),(0,14),(1,3),(1,4),(1,7),(1,9),(1,14),(3,4),(3,7),(3,9),(3,14),(4,7),(4,9),(4,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1326_q : Finset ℕ := ([0,1,3,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1326_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,7),(0,10),(0,13),(1,3),(1,4),(1,7),(1,10),(1,13),(3,4),(3,7),(3,10),(3,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1327_q : Finset ℕ := ([0,1,3,4,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1327_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,10),(0,14),(1,3),(1,4),(1,7),(1,10),(1,14),(3,4),(3,7),(3,10),(3,14),(4,7),(4,10),(4,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1328_q : Finset ℕ := ([0,1,3,4,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1328_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,11),(0,14),(1,3),(1,4),(1,7),(1,11),(1,14),(3,4),(3,7),(3,11),(3,14),(4,7),(4,11),(4,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1329_q : Finset ℕ := ([0,1,3,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1329_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,8),(0,9),(0,13),(1,3),(1,4),(1,8),(1,9),(1,13),(3,4),(3,8),(3,9),(3,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1330_q : Finset ℕ := ([0,1,3,4,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1330_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,8),(0,9),(0,14),(1,3),(1,4),(1,8),(1,9),(1,14),(3,4),(3,8),(3,9),(3,14),(4,8),(4,9),(4,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1331_q : Finset ℕ := ([0,1,3,4,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1331_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,8),(0,10),(0,14),(1,3),(1,4),(1,8),(1,10),(1,14),(3,4),(3,8),(3,10),(3,14),(4,8),(4,10),(4,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1332_q : Finset ℕ := ([0,1,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1332_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(1,3),(1,5),(1,6),(1,8),(1,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1333_q : Finset ℕ := ([0,1,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1333_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(1,3),(1,5),(1,6),(1,8),(1,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1334_q : Finset ℕ := ([0,1,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1334_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(1,3),(1,5),(1,6),(1,8),(1,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1335_q : Finset ℕ := ([0,1,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1335_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,13),(1,3),(1,5),(1,6),(1,8),(1,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1336_q : Finset ℕ := ([0,1,3,5,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1336_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,14),(1,3),(1,5),(1,6),(1,8),(1,14),(3,5),(3,6),(3,8),(3,14),(5,6),(5,8),(5,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1337_q : Finset ℕ := ([0,1,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1337_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,9),(0,12),(1,3),(1,5),(1,6),(1,9),(1,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1338_q : Finset ℕ := ([0,1,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1338_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,9),(0,13),(1,3),(1,5),(1,6),(1,9),(1,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1339_q : Finset ℕ := ([0,1,3,5,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1339_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,14),(1,3),(1,5),(1,6),(1,9),(1,14),(3,5),(3,6),(3,9),(3,14),(5,6),(5,9),(5,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1340_q : Finset ℕ := ([0,1,3,5,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1340_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,10),(0,14),(1,3),(1,5),(1,6),(1,10),(1,14),(3,5),(3,6),(3,10),(3,14),(5,6),(5,10),(5,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1341_q : Finset ℕ := ([0,1,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1341_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(1,3),(1,5),(1,7),(1,8),(1,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1342_q : Finset ℕ := ([0,1,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1342_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,8),(0,12),(1,3),(1,5),(1,7),(1,8),(1,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1343_q : Finset ℕ := ([0,1,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1343_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,8),(0,13),(1,3),(1,5),(1,7),(1,8),(1,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

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

noncomputable def certificate_1344_q : Finset ℕ := ([0,1,3,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1344_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,14),(1,3),(1,5),(1,7),(1,8),(1,14),(3,5),(3,7),(3,8),(3,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1345_q : Finset ℕ := ([0,1,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1345_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(1,3),(1,5),(1,7),(1,9),(1,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1346_q : Finset ℕ := ([0,1,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1346_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(1,3),(1,5),(1,7),(1,9),(1,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1347_q : Finset ℕ := ([0,1,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1347_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,13),(1,3),(1,5),(1,7),(1,9),(1,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1348_q : Finset ℕ := ([0,1,3,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1348_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,14),(1,3),(1,5),(1,7),(1,9),(1,14),(3,5),(3,7),(3,9),(3,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1349_q : Finset ℕ := ([0,1,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1349_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(1,3),(1,5),(1,7),(1,10),(1,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1350_q : Finset ℕ := ([0,1,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1350_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,10),(0,13),(1,3),(1,5),(1,7),(1,10),(1,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1351_q : Finset ℕ := ([0,1,3,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1351_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,14),(1,3),(1,5),(1,7),(1,10),(1,14),(3,5),(3,7),(3,10),(3,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1352_q : Finset ℕ := ([0,1,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1352_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,11),(0,13),(1,3),(1,5),(1,7),(1,11),(1,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1353_q : Finset ℕ := ([0,1,3,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1353_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,11),(0,14),(1,3),(1,5),(1,7),(1,11),(1,14),(3,5),(3,7),(3,11),(3,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1354_q : Finset ℕ := ([0,1,3,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1354_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,12),(0,14),(1,3),(1,5),(1,7),(1,12),(1,14),(3,5),(3,7),(3,12),(3,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1355_q : Finset ℕ := ([0,1,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1355_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,9),(0,12),(1,3),(1,5),(1,8),(1,9),(1,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1356_q : Finset ℕ := ([0,1,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1356_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,8),(0,9),(0,13),(1,3),(1,5),(1,8),(1,9),(1,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1357_q : Finset ℕ := ([0,1,3,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1357_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,9),(0,14),(1,3),(1,5),(1,8),(1,9),(1,14),(3,5),(3,8),(3,9),(3,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1358_q : Finset ℕ := ([0,1,3,5,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1358_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,8),(0,10),(0,12),(1,3),(1,5),(1,8),(1,10),(1,12),(3,5),(3,8),(3,10),(3,12),(5,8),(5,10),(5,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1359_q : Finset ℕ := ([0,1,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1359_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,8),(0,10),(0,13),(1,3),(1,5),(1,8),(1,10),(1,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1360_q : Finset ℕ := ([0,1,3,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1360_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,10),(0,14),(1,3),(1,5),(1,8),(1,10),(1,14),(3,5),(3,8),(3,10),(3,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1361_q : Finset ℕ := ([0,1,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1361_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,8),(0,11),(0,13),(1,3),(1,5),(1,8),(1,11),(1,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1362_q : Finset ℕ := ([0,1,3,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1362_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,11),(0,14),(1,3),(1,5),(1,8),(1,11),(1,14),(3,5),(3,8),(3,11),(3,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1363_q : Finset ℕ := ([0,1,3,5,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1363_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,12),(0,14),(1,3),(1,5),(1,8),(1,12),(1,14),(3,5),(3,8),(3,12),(3,14),(5,8),(5,12),(5,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1364_q : Finset ℕ := ([0,1,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1364_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,9),(0,10),(0,13),(1,3),(1,5),(1,9),(1,10),(1,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1365_q : Finset ℕ := ([0,1,3,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1365_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,9),(0,10),(0,14),(1,3),(1,5),(1,9),(1,10),(1,14),(3,5),(3,9),(3,10),(3,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1366_q : Finset ℕ := ([0,1,3,5,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1366_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,9),(0,11),(0,13),(1,3),(1,5),(1,9),(1,11),(1,13),(3,5),(3,9),(3,11),(3,13),(5,9),(5,11),(5,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1367_q : Finset ℕ := ([0,1,3,5,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1367_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,9),(0,11),(0,14),(1,3),(1,5),(1,9),(1,11),(1,14),(3,5),(3,9),(3,11),(3,14),(5,9),(5,11),(5,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1368_q : Finset ℕ := ([0,1,3,5,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1368_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,9),(0,12),(0,14),(1,3),(1,5),(1,9),(1,12),(1,14),(3,5),(3,9),(3,12),(3,14),(5,9),(5,12),(5,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1369_q : Finset ℕ := ([0,1,3,5,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1369_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,10),(0,11),(0,14),(1,3),(1,5),(1,10),(1,11),(1,14),(3,5),(3,10),(3,11),(3,14),(5,10),(5,11),(5,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1370_q : Finset ℕ := ([0,1,3,5,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1370_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,10),(0,12),(0,14),(1,3),(1,5),(1,10),(1,12),(1,14),(3,5),(3,10),(3,12),(3,14),(5,10),(5,12),(5,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1371_q : Finset ℕ := ([0,1,3,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1371_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(1,3),(1,6),(1,7),(1,9),(1,12),(3,6),(3,7),(3,9),(3,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1372_q : Finset ℕ := ([0,1,3,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1372_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,7),(0,9),(0,13),(1,3),(1,6),(1,7),(1,9),(1,13),(3,6),(3,7),(3,9),(3,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1373_q : Finset ℕ := ([0,1,3,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1373_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,9),(0,14),(1,3),(1,6),(1,7),(1,9),(1,14),(3,6),(3,7),(3,9),(3,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1374_q : Finset ℕ := ([0,1,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1374_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,7),(0,10),(0,13),(1,3),(1,6),(1,7),(1,10),(1,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1375_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,10),(0,14),(1,3),(1,6),(1,7),(1,10),(1,14),(3,6),(3,7),(3,10),(3,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_9_5_1 : List (List (List ℕ)) := [[[1],[1,1]],[[1],[1,2]],[[1,1],[2]],[[1,1,1,1]]]

end CycleClique

end OAI
end


