-- Prove2me | Definitions.Def_OAIQ107D002
-- name    : OAIQ107D002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:37:51.698541+00:00
-- url     : https://prove2.me/theorems/758965d2-5bba-4345-bd22-fa4b17071819
-- title:
--   Definitions bundle OAIQ107D002 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 695 declarations of OpenAI's Lean: 694 definitions and 1 instance. The definitions and types are `OAI.CycleClique.certificate_1375_q`, `OAI.CycleClique.certificate_1376_edges`, `OAI.CycleClique.certificate_1376_q`, `OAI.CycleClique.certificate_1377_edges`, `OAI.CycleClique.certificate_1377_q`, `OAI.CycleClique.certificate_1378_edges`, `OAI.CycleClique.certificate_1378_q`, `OAI.CycleClique.certificate_1379_edges`, `OAI.CycleClique.certificate_1379_q`, `OAI.CycleClique.certificate_137_edges`, `OAI.CycleClique.certificate_137_q`, `OAI.CycleClique.certificate_1380_edges`, `OAI.CycleClique.certificate_1380_q`, `OAI.CycleClique.certificate_1381_edges`, `OAI.CycleClique.certificate_1381_q`, `OAI.CycleClique.certificate_1382_edges`, `OAI.CycleClique.certificate_1382_q`, `OAI.CycleClique.certificate_1383_edges`, `OAI.CycleClique.certificate_1383_q`, `OAI.CycleClique.certificate_1384_edges`, `OAI.CycleClique.certificate_1384_q`, `OAI.CycleClique.certificate_1385_edges`, `OAI.CycleClique.certificate_1385_q`, `OAI.CycleClique.certificate_1386_edges`, `OAI.CycleClique.certificate_1386_q`, `OAI.CycleClique.certificate_1387_edges`, `OAI.CycleClique.certificate_1387_q`, `OAI.CycleClique.certificate_1388_edges`, `OAI.CycleClique.certificate_1388_q`, `OAI.CycleClique.certificate_1389_edges`, `OAI.CycleClique.certificate_1389_q`, `OAI.CycleClique.certificate_138_edges`, `OAI.CycleClique.certificate_138_q`, `OAI.CycleClique.certificate_1390_edges`, `OAI.CycleClique.certificate_1390_q`, `OAI.CycleClique.certificate_1391_edges`, `OAI.CycleClique.certificate_1391_q`, `OAI.CycleClique.certificate_1392_edges`, `OAI.CycleClique.certificate_1392_q`, `OAI.CycleClique.certificate_1393_edges` and 654 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates005`, `Ramsey_CycleClique_Certificates006`, `Ramsey_CycleClique_Certificates043`, `Ramsey_CycleClique_Certificates044`, `Ramsey_CycleClique_Certificates045`, `Ramsey_CycleClique_Certificates046`, `Ramsey_CycleClique_Certificates047`, `Ramsey_CycleClique_Certificates048`, `Ramsey_CycleClique_Certificates049`, `Ramsey_CycleClique_Certificates050`, `Ramsey_CycleClique_Certificates051`, `Ramsey_CycleClique_Certificates052`, `Ramsey_CycleClique_Certificates053`, `Ramsey_CycleClique_CliqueBits`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D017`, `OAIQ107D018`, `OAIQ107D019`, `OAIQ107D022`, `OAIQ107D027`, `OAIQ107D028`, `OAIQ107D029`, `OAIQ107D030`, `OAIQ107D033`, `OAIQ107D034`, `OAIQ107D035`, `OAIQ107D037`, `OAIQ107D038`, `OAIQ107D039`, `OAIQ107D040` and `OAIQ107D046`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CliqueBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

instance instCommutativeNatLor_solutions : Std.Commutative Nat.lor := ⟨Nat.lor_comm⟩

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

noncomputable def certificate_13_q : Finset ℕ := ([0,1,2,3] : List ℕ).toFinset
noncomputable def certificate_13_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def certificate_14_q : Finset ℕ := ([0,1,2,4] : List ℕ).toFinset
noncomputable def certificate_14_edges : List (ℕ × ℕ) := [(2,3),(3,4),(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)]

noncomputable def certificate_15_q : Finset ℕ := ([0,1,2,5] : List ℕ).toFinset

noncomputable def certificate_15_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(0,1),(0,2),(0,5),(1,2),(1,5),(2,5)]

noncomputable def certificate_15_E : List (ℕ × ℕ) := certificate_15_edges

noncomputable def certificate_15_part_1_E : List (ℕ × ℕ) := certificate_15_E

noncomputable def certificate_15_part_2_E : List (ℕ × ℕ) := certificate_15_part_1_E

noncomputable def certificate_15_part_4_E : List (ℕ × ℕ) := certificate_15_part_2_E

noncomputable def certificate_15_part_5_E : List (ℕ × ℕ) := certificate_15_part_4_E

noncomputable def certificate_15_part_7_E : List (ℕ × ℕ) := certificate_15_part_5_E

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

noncomputable def certificate_137_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_137_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_138_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_138_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_139_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_139_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_140_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_140_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_141_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_141_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_142_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_142_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_143_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_143_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_144_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_144_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_145_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_145_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_146_q : Finset ℕ := ([0,1,2,3,6] : List ℕ).toFinset
noncomputable def certificate_146_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_147_q : Finset ℕ := ([0,1,2,3,7] : List ℕ).toFinset
noncomputable def certificate_147_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,7),(1,2),(1,3),(1,7),(2,3),(2,7),(3,7)]

noncomputable def certificate_148_q : Finset ℕ := ([0,1,2,3,8] : List ℕ).toFinset

noncomputable def certificate_148_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,8),(1,2),(1,3),(1,8),(2,3),(2,8),(3,8)]

noncomputable def certificate_148_E : List (ℕ × ℕ) := certificate_148_edges

noncomputable def certificate_148_part_1_E : List (ℕ × ℕ) := certificate_148_E

noncomputable def certificate_148_part_2_E : List (ℕ × ℕ) := certificate_148_part_1_E

noncomputable def certificate_148_part_3_E : List (ℕ × ℕ) := certificate_148_part_2_E

noncomputable def certificate_148_part_4_E : List (ℕ × ℕ) := certificate_148_part_3_E

noncomputable def certificate_148_part_6_E : List (ℕ × ℕ) := certificate_148_part_4_E

noncomputable def certificate_148_part_7_E : List (ℕ × ℕ) := certificate_148_part_6_E

noncomputable def certificate_148_part_11_E : List (ℕ × ℕ) := certificate_148_part_7_E

noncomputable def certificate_149_q : Finset ℕ := ([0,1,2,3,9] : List ℕ).toFinset

noncomputable def certificate_149_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,9),(1,2),(1,3),(1,9),(2,3),(2,9),(3,9)]

noncomputable def certificate_149_E : List (ℕ × ℕ) := certificate_149_edges

noncomputable def certificate_149_part_1_E : List (ℕ × ℕ) := certificate_149_E

noncomputable def certificate_149_part_2_E : List (ℕ × ℕ) := certificate_149_part_1_E

noncomputable def certificate_149_part_3_E : List (ℕ × ℕ) := certificate_149_part_2_E

noncomputable def certificate_149_part_4_E : List (ℕ × ℕ) := certificate_149_part_3_E

noncomputable def certificate_149_part_6_E : List (ℕ × ℕ) := certificate_149_part_4_E

noncomputable def certificate_149_part_7_E : List (ℕ × ℕ) := certificate_149_part_6_E

noncomputable def certificate_149_part_10_E : List (ℕ × ℕ) := certificate_149_part_7_E

noncomputable def certificate_149_part_13_E : List (ℕ × ℕ) := certificate_149_part_10_E

noncomputable def certificate_149_part_14_E : List (ℕ × ℕ) := certificate_149_part_13_E

noncomputable def certificate_149_part_21_E : List (ℕ × ℕ) := certificate_149_part_14_E

noncomputable def certificate_149_part_24_E : List (ℕ × ℕ) := certificate_149_part_21_E

noncomputable def certificate_149_part_25_E : List (ℕ × ℕ) := certificate_149_part_24_E

noncomputable def certificate_149_part_28_E : List (ℕ × ℕ) := certificate_149_part_25_E

noncomputable def certificate_149_part_29_E : List (ℕ × ℕ) := certificate_149_part_28_E

noncomputable def certificate_149_part_33_E : List (ℕ × ℕ) := certificate_149_part_29_E

noncomputable def certificate_149_part_34_E : List (ℕ × ℕ) := certificate_149_part_33_E

noncomputable def certificate_149_part_41_E : List (ℕ × ℕ) := certificate_149_part_34_E

noncomputable def certificate_149_part_49_E : List (ℕ × ℕ) := certificate_149_part_41_E

noncomputable def certificate_149_part_50_E : List (ℕ × ℕ) := certificate_149_part_49_E

noncomputable def certificate_149_part_58_E : List (ℕ × ℕ) := certificate_149_part_50_E

noncomputable def certificate_150_q : Finset ℕ := ([0,1,2,4,6] : List ℕ).toFinset
noncomputable def certificate_150_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,4),(0,6),(1,2),(1,4),(1,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_151_q : Finset ℕ := ([0,1,2,4,7] : List ℕ).toFinset
noncomputable def certificate_151_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,4),(0,7),(1,2),(1,4),(1,7),(2,4),(2,7),(4,7)]

noncomputable def certificate_152_q : Finset ℕ := ([0,1,2,4,8] : List ℕ).toFinset
noncomputable def certificate_152_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,8),(1,2),(1,4),(1,8),(2,4),(2,8),(4,8)]

noncomputable def certificate_153_q : Finset ℕ := ([0,1,2,4,9] : List ℕ).toFinset
noncomputable def certificate_153_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,9),(1,2),(1,4),(1,9),(2,4),(2,9),(4,9)]

noncomputable def certificate_154_q : Finset ℕ := ([0,1,2,5,8] : List ℕ).toFinset
noncomputable def certificate_154_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,5),(0,8),(1,2),(1,5),(1,8),(2,5),(2,8),(5,8)]

noncomputable def certificate_155_q : Finset ℕ := ([0,1,2,5,9] : List ℕ).toFinset
noncomputable def certificate_155_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,5),(0,9),(1,2),(1,5),(1,9),(2,5),(2,9),(5,9)]

noncomputable def certificate_156_q : Finset ℕ := ([0,1,3,4,6] : List ℕ).toFinset
noncomputable def certificate_156_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(0,1),(0,3),(0,4),(0,6),(1,3),(1,4),(1,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_157_q : Finset ℕ := ([0,1,3,4,7] : List ℕ).toFinset
noncomputable def certificate_157_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(0,1),(0,3),(0,4),(0,7),(1,3),(1,4),(1,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_158_q : Finset ℕ := ([0,1,3,4,8] : List ℕ).toFinset
noncomputable def certificate_158_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,8),(1,3),(1,4),(1,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_159_q : Finset ℕ := ([0,1,3,4,9] : List ℕ).toFinset

noncomputable def certificate_159_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,4),(0,9),(1,3),(1,4),(1,9),(3,4),(3,9),(4,9)]

noncomputable def certificate_159_E : List (ℕ × ℕ) := certificate_159_edges

noncomputable def certificate_159_part_1_E : List (ℕ × ℕ) := certificate_159_E

noncomputable def certificate_159_part_2_E : List (ℕ × ℕ) := certificate_159_part_1_E

noncomputable def certificate_159_part_3_E : List (ℕ × ℕ) := certificate_159_part_2_E

noncomputable def certificate_159_part_4_E : List (ℕ × ℕ) := certificate_159_part_3_E

noncomputable def certificate_159_part_5_E : List (ℕ × ℕ) := certificate_159_part_4_E

noncomputable def certificate_159_part_6_E : List (ℕ × ℕ) := certificate_159_part_5_E

noncomputable def certificate_159_part_7_E : List (ℕ × ℕ) := certificate_159_part_6_E

noncomputable def certificate_159_part_10_E : List (ℕ × ℕ) := certificate_159_part_7_E

noncomputable def certificate_159_part_11_E : List (ℕ × ℕ) := certificate_159_part_10_E

noncomputable def certificate_159_part_12_E : List (ℕ × ℕ) := certificate_159_part_11_E

noncomputable def certificate_159_part_14_E : List (ℕ × ℕ) := certificate_159_part_12_E

noncomputable def certificate_159_part_15_E : List (ℕ × ℕ) := certificate_159_part_14_E

noncomputable def certificate_159_part_20_E : List (ℕ × ℕ) := certificate_159_part_15_E

noncomputable def certificate_159_part_21_E : List (ℕ × ℕ) := certificate_159_part_20_E

noncomputable def certificate_159_part_25_E : List (ℕ × ℕ) := certificate_159_part_21_E

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_160_q : Finset ℕ := ([0,1,3,5,7] : List ℕ).toFinset
noncomputable def certificate_160_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,3),(0,5),(0,7),(1,3),(1,5),(1,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_161_q : Finset ℕ := ([0,1,3,5,8] : List ℕ).toFinset
noncomputable def certificate_161_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,5),(0,8),(1,3),(1,5),(1,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_162_q : Finset ℕ := ([0,1,3,5,9] : List ℕ).toFinset
noncomputable def certificate_162_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,9),(1,3),(1,5),(1,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_163_q : Finset ℕ := ([0,1,3,6,8] : List ℕ).toFinset
noncomputable def certificate_163_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,6),(0,8),(1,3),(1,6),(1,8),(3,6),(3,8),(6,8)]

noncomputable def certificate_164_q : Finset ℕ := ([0,1,3,6,9] : List ℕ).toFinset
noncomputable def certificate_164_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,6),(0,9),(1,3),(1,6),(1,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_165_q : Finset ℕ := ([0,1,3,7,9] : List ℕ).toFinset
noncomputable def certificate_165_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,7),(0,9),(1,3),(1,7),(1,9),(3,7),(3,9),(7,9)]

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

noncomputable def certificate_1375_q : Finset ℕ := ([0,1,3,6,7,10,14] : List ℕ).toFinset

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates044
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1376_q : Finset ℕ := ([0,1,3,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1376_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,6),(0,8),(0,9),(0,12),(1,3),(1,6),(1,8),(1,9),(1,12),(3,6),(3,8),(3,9),(3,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1377_q : Finset ℕ := ([0,1,3,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1377_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,8),(0,9),(0,13),(1,3),(1,6),(1,8),(1,9),(1,13),(3,6),(3,8),(3,9),(3,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1378_q : Finset ℕ := ([0,1,3,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1378_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,8),(0,9),(0,14),(1,3),(1,6),(1,8),(1,9),(1,14),(3,6),(3,8),(3,9),(3,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1379_q : Finset ℕ := ([0,1,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1379_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,8),(0,10),(0,13),(1,3),(1,6),(1,8),(1,10),(1,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1380_q : Finset ℕ := ([0,1,3,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1380_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,8),(0,10),(0,14),(1,3),(1,6),(1,8),(1,10),(1,14),(3,6),(3,8),(3,10),(3,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1381_q : Finset ℕ := ([0,1,3,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1381_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,8),(0,11),(0,13),(1,3),(1,6),(1,8),(1,11),(1,13),(3,6),(3,8),(3,11),(3,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1382_q : Finset ℕ := ([0,1,3,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1382_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,8),(0,11),(0,14),(1,3),(1,6),(1,8),(1,11),(1,14),(3,6),(3,8),(3,11),(3,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1383_q : Finset ℕ := ([0,1,3,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1383_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,8),(0,12),(0,14),(1,3),(1,6),(1,8),(1,12),(1,14),(3,6),(3,8),(3,12),(3,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1384_q : Finset ℕ := ([0,1,3,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1384_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,6),(0,9),(0,10),(0,13),(1,3),(1,6),(1,9),(1,10),(1,13),(3,6),(3,9),(3,10),(3,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1385_q : Finset ℕ := ([0,1,3,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1385_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,9),(0,10),(0,14),(1,3),(1,6),(1,9),(1,10),(1,14),(3,6),(3,9),(3,10),(3,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1386_q : Finset ℕ := ([0,1,3,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1386_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,9),(0,11),(0,14),(1,3),(1,6),(1,9),(1,11),(1,14),(3,6),(3,9),(3,11),(3,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1387_q : Finset ℕ := ([0,1,3,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1387_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,9),(0,12),(0,14),(1,3),(1,6),(1,9),(1,12),(1,14),(3,6),(3,9),(3,12),(3,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1388_q : Finset ℕ := ([0,1,3,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1388_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,10),(0,11),(0,14),(1,3),(1,6),(1,10),(1,11),(1,14),(3,6),(3,10),(3,11),(3,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1389_q : Finset ℕ := ([0,1,3,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1389_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,7),(0,8),(0,10),(0,14),(1,3),(1,7),(1,8),(1,10),(1,14),(3,7),(3,8),(3,10),(3,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1390_q : Finset ℕ := ([0,1,3,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1390_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,7),(0,8),(0,11),(0,14),(1,3),(1,7),(1,8),(1,11),(1,14),(3,7),(3,8),(3,11),(3,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1391_q : Finset ℕ := ([0,1,3,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1391_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,7),(0,9),(0,10),(0,13),(1,3),(1,7),(1,9),(1,10),(1,13),(3,7),(3,9),(3,10),(3,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1392_q : Finset ℕ := ([0,1,3,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1392_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,7),(0,9),(0,10),(0,14),(1,3),(1,7),(1,9),(1,10),(1,14),(3,7),(3,9),(3,10),(3,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1393_q : Finset ℕ := ([0,1,3,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1393_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,7),(0,9),(0,11),(0,14),(1,3),(1,7),(1,9),(1,11),(1,14),(3,7),(3,9),(3,11),(3,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1394_q : Finset ℕ := ([0,1,3,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1394_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,7),(0,10),(0,11),(0,14),(1,3),(1,7),(1,10),(1,11),(1,14),(3,7),(3,10),(3,11),(3,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1395_q : Finset ℕ := ([0,1,3,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1395_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,8),(0,10),(0,11),(0,14),(1,3),(1,8),(1,10),(1,11),(1,14),(3,8),(3,10),(3,11),(3,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1396_q : Finset ℕ := ([0,1,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1396_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,4),(0,5),(0,8),(0,9),(0,12),(1,4),(1,5),(1,8),(1,9),(1,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1397_q : Finset ℕ := ([0,1,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1397_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,4),(0,5),(0,8),(0,9),(0,13),(1,4),(1,5),(1,8),(1,9),(1,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1398_q : Finset ℕ := ([0,1,4,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1398_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,5),(0,8),(0,9),(0,14),(1,4),(1,5),(1,8),(1,9),(1,14),(4,5),(4,8),(4,9),(4,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1399_q : Finset ℕ := ([0,1,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1399_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,4),(0,5),(0,8),(0,10),(0,13),(1,4),(1,5),(1,8),(1,10),(1,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1400_q : Finset ℕ := ([0,1,4,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1400_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,5),(0,8),(0,10),(0,14),(1,4),(1,5),(1,8),(1,10),(1,14),(4,5),(4,8),(4,10),(4,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1401_q : Finset ℕ := ([0,1,4,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1401_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,5),(0,8),(0,11),(0,14),(1,4),(1,5),(1,8),(1,11),(1,14),(4,5),(4,8),(4,11),(4,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1402_q : Finset ℕ := ([0,1,4,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1402_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,5),(0,9),(0,10),(0,14),(1,4),(1,5),(1,9),(1,10),(1,14),(4,5),(4,9),(4,10),(4,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1403_q : Finset ℕ := ([0,1,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1403_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,4),(0,6),(0,8),(0,10),(0,13),(1,4),(1,6),(1,8),(1,10),(1,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1404_q : Finset ℕ := ([0,1,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1404_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,6),(0,8),(0,10),(0,14),(1,4),(1,6),(1,8),(1,10),(1,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1405_q : Finset ℕ := ([0,1,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1405_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,6),(0,8),(0,11),(0,14),(1,4),(1,6),(1,8),(1,11),(1,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1406_q : Finset ℕ := ([0,1,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1406_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,6),(0,9),(0,10),(0,14),(1,4),(1,6),(1,9),(1,10),(1,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1407_q : Finset ℕ := ([0,1,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1407_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,6),(0,9),(0,11),(0,14),(1,4),(1,6),(1,9),(1,11),(1,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates045
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1408_q : Finset ℕ := ([0,1,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1408_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,4),(0,7),(0,8),(0,11),(0,14),(1,4),(1,7),(1,8),(1,11),(1,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1409_q : Finset ℕ := ([0,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1409_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1410_q : Finset ℕ := ([0,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1410_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1411_q : Finset ℕ := ([0,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1411_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1412_q : Finset ℕ := ([0,2,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1412_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(2,3),(2,5),(2,6),(2,8),(2,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1413_q : Finset ℕ := ([0,2,3,5,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1413_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,14),(2,3),(2,5),(2,6),(2,8),(2,14),(3,5),(3,6),(3,8),(3,14),(5,6),(5,8),(5,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1414_q : Finset ℕ := ([0,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1414_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1415_q : Finset ℕ := ([0,2,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1415_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(2,3),(2,5),(2,6),(2,9),(2,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1416_q : Finset ℕ := ([0,2,3,5,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1416_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,14),(2,3),(2,5),(2,6),(2,9),(2,14),(3,5),(3,6),(3,9),(3,14),(5,6),(5,9),(5,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1417_q : Finset ℕ := ([0,2,3,5,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1417_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,10),(0,14),(2,3),(2,5),(2,6),(2,10),(2,14),(3,5),(3,6),(3,10),(3,14),(5,6),(5,10),(5,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1418_q : Finset ℕ := ([0,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1418_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1419_q : Finset ℕ := ([0,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1419_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1420_q : Finset ℕ := ([0,2,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1420_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,8),(0,13),(2,3),(2,5),(2,7),(2,8),(2,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1421_q : Finset ℕ := ([0,2,3,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1421_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,14),(2,3),(2,5),(2,7),(2,8),(2,14),(3,5),(3,7),(3,8),(3,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1422_q : Finset ℕ := ([0,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1422_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1423_q : Finset ℕ := ([0,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1423_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1424_q : Finset ℕ := ([0,2,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1424_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(2,3),(2,5),(2,7),(2,9),(2,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1425_q : Finset ℕ := ([0,2,3,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1425_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,14),(2,3),(2,5),(2,7),(2,9),(2,14),(3,5),(3,7),(3,9),(3,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1426_q : Finset ℕ := ([0,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1426_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1427_q : Finset ℕ := ([0,2,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1427_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(2,3),(2,5),(2,7),(2,10),(2,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1428_q : Finset ℕ := ([0,2,3,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1428_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,14),(2,3),(2,5),(2,7),(2,10),(2,14),(3,5),(3,7),(3,10),(3,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1429_q : Finset ℕ := ([0,2,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1429_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(2,3),(2,5),(2,7),(2,11),(2,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1430_q : Finset ℕ := ([0,2,3,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1430_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,11),(0,14),(2,3),(2,5),(2,7),(2,11),(2,14),(3,5),(3,7),(3,11),(3,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1431_q : Finset ℕ := ([0,2,3,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1431_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,12),(0,14),(2,3),(2,5),(2,7),(2,12),(2,14),(3,5),(3,7),(3,12),(3,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1432_q : Finset ℕ := ([0,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1432_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1433_q : Finset ℕ := ([0,2,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1433_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,8),(0,9),(0,13),(2,3),(2,5),(2,8),(2,9),(2,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1434_q : Finset ℕ := ([0,2,3,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1434_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,9),(0,14),(2,3),(2,5),(2,8),(2,9),(2,14),(3,5),(3,8),(3,9),(3,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1435_q : Finset ℕ := ([0,2,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1435_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(2,3),(2,5),(2,8),(2,10),(2,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1436_q : Finset ℕ := ([0,2,3,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1436_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,10),(0,14),(2,3),(2,5),(2,8),(2,10),(2,14),(3,5),(3,8),(3,10),(3,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1437_q : Finset ℕ := ([0,2,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1437_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(2,3),(2,5),(2,8),(2,11),(2,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1438_q : Finset ℕ := ([0,2,3,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1438_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,11),(0,14),(2,3),(2,5),(2,8),(2,11),(2,14),(3,5),(3,8),(3,11),(3,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1439_q : Finset ℕ := ([0,2,3,5,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1439_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,12),(0,14),(2,3),(2,5),(2,8),(2,12),(2,14),(3,5),(3,8),(3,12),(3,14),(5,8),(5,12),(5,14),(8,12),(8,14),(12,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates046
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1440_q : Finset ℕ := ([0,2,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1440_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(2,3),(2,5),(2,9),(2,10),(2,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1441_q : Finset ℕ := ([0,2,3,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1441_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,9),(0,10),(0,14),(2,3),(2,5),(2,9),(2,10),(2,14),(3,5),(3,9),(3,10),(3,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1442_q : Finset ℕ := ([0,2,3,5,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1442_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,9),(0,11),(0,14),(2,3),(2,5),(2,9),(2,11),(2,14),(3,5),(3,9),(3,11),(3,14),(5,9),(5,11),(5,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1443_q : Finset ℕ := ([0,2,3,5,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1443_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,10),(0,11),(0,14),(2,3),(2,5),(2,10),(2,11),(2,14),(3,5),(3,10),(3,11),(3,14),(5,10),(5,11),(5,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1444_q : Finset ℕ := ([0,2,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1444_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(2,3),(2,6),(2,7),(2,10),(2,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1445_q : Finset ℕ := ([0,2,3,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1445_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,7),(0,10),(0,14),(2,3),(2,6),(2,7),(2,10),(2,14),(3,6),(3,7),(3,10),(3,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1446_q : Finset ℕ := ([0,2,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1446_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(2,3),(2,6),(2,8),(2,10),(2,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1447_q : Finset ℕ := ([0,2,3,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1447_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,8),(0,10),(0,14),(2,3),(2,6),(2,8),(2,10),(2,14),(3,6),(3,8),(3,10),(3,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1448_q : Finset ℕ := ([0,2,3,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1448_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,8),(0,11),(0,14),(2,3),(2,6),(2,8),(2,11),(2,14),(3,6),(3,8),(3,11),(3,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1449_q : Finset ℕ := ([0,2,3,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1449_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,9),(0,10),(0,14),(2,3),(2,6),(2,9),(2,10),(2,14),(3,6),(3,9),(3,10),(3,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1450_q : Finset ℕ := ([0,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1450_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1451_q : Finset ℕ := ([0,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1451_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1452_q : Finset ℕ := ([0,2,4,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1452_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(2,4),(2,5),(2,7),(2,9),(2,13),(4,5),(4,7),(4,9),(4,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1453_q : Finset ℕ := ([0,2,4,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1453_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,14),(2,4),(2,5),(2,7),(2,9),(2,14),(4,5),(4,7),(4,9),(4,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1454_q : Finset ℕ := ([0,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1454_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1455_q : Finset ℕ := ([0,2,4,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1455_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(2,4),(2,5),(2,7),(2,10),(2,13),(4,5),(4,7),(4,10),(4,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1456_q : Finset ℕ := ([0,2,4,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1456_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,10),(0,14),(2,4),(2,5),(2,7),(2,10),(2,14),(4,5),(4,7),(4,10),(4,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1457_q : Finset ℕ := ([0,2,4,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1457_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(2,4),(2,5),(2,7),(2,11),(2,13),(4,5),(4,7),(4,11),(4,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1458_q : Finset ℕ := ([0,2,4,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1458_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,11),(0,14),(2,4),(2,5),(2,7),(2,11),(2,14),(4,5),(4,7),(4,11),(4,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1459_q : Finset ℕ := ([0,2,4,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1459_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,12),(0,14),(2,4),(2,5),(2,7),(2,12),(2,14),(4,5),(4,7),(4,12),(4,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1460_q : Finset ℕ := ([0,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1460_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1461_q : Finset ℕ := ([0,2,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1461_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,8),(0,9),(0,13),(2,4),(2,5),(2,8),(2,9),(2,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1462_q : Finset ℕ := ([0,2,4,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1462_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,8),(0,9),(0,14),(2,4),(2,5),(2,8),(2,9),(2,14),(4,5),(4,8),(4,9),(4,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1463_q : Finset ℕ := ([0,2,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1463_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(2,4),(2,5),(2,8),(2,10),(2,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1464_q : Finset ℕ := ([0,2,4,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1464_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,8),(0,10),(0,14),(2,4),(2,5),(2,8),(2,10),(2,14),(4,5),(4,8),(4,10),(4,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1465_q : Finset ℕ := ([0,2,4,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1465_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,8),(0,11),(0,14),(2,4),(2,5),(2,8),(2,11),(2,14),(4,5),(4,8),(4,11),(4,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1466_q : Finset ℕ := ([0,2,4,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1466_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,9),(0,10),(0,14),(2,4),(2,5),(2,9),(2,10),(2,14),(4,5),(4,9),(4,10),(4,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1467_q : Finset ℕ := ([0,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1467_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1468_q : Finset ℕ := ([0,2,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1468_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(2,4),(2,6),(2,7),(2,9),(2,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1469_q : Finset ℕ := ([0,2,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1469_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,14),(2,4),(2,6),(2,7),(2,9),(2,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1470_q : Finset ℕ := ([0,2,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1470_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(2,4),(2,6),(2,7),(2,10),(2,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1471_q : Finset ℕ := ([0,2,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1471_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,10),(0,14),(2,4),(2,6),(2,7),(2,10),(2,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates047
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1472_q : Finset ℕ := ([0,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1472_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1473_q : Finset ℕ := ([0,2,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1473_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,8),(0,9),(0,13),(2,4),(2,6),(2,8),(2,9),(2,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1474_q : Finset ℕ := ([0,2,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1474_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,9),(0,14),(2,4),(2,6),(2,8),(2,9),(2,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1475_q : Finset ℕ := ([0,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1475_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1476_q : Finset ℕ := ([0,2,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1476_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(2,4),(2,6),(2,8),(2,10),(2,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1477_q : Finset ℕ := ([0,2,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1477_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,14),(2,4),(2,6),(2,8),(2,10),(2,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1478_q : Finset ℕ := ([0,2,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1478_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(2,4),(2,6),(2,8),(2,11),(2,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1479_q : Finset ℕ := ([0,2,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1479_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,11),(0,14),(2,4),(2,6),(2,8),(2,11),(2,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1480_q : Finset ℕ := ([0,2,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1480_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,12),(0,14),(2,4),(2,6),(2,8),(2,12),(2,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1481_q : Finset ℕ := ([0,2,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1481_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(2,4),(2,6),(2,9),(2,10),(2,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1482_q : Finset ℕ := ([0,2,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1482_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,9),(0,10),(0,14),(2,4),(2,6),(2,9),(2,10),(2,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1483_q : Finset ℕ := ([0,2,4,6,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1483_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(2,4),(2,6),(2,9),(2,11),(2,13),(4,6),(4,9),(4,11),(4,13),(6,9),(6,11),(6,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1484_q : Finset ℕ := ([0,2,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1484_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,9),(0,11),(0,14),(2,4),(2,6),(2,9),(2,11),(2,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1485_q : Finset ℕ := ([0,2,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1485_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,9),(0,12),(0,14),(2,4),(2,6),(2,9),(2,12),(2,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1486_q : Finset ℕ := ([0,2,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1486_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,10),(0,11),(0,14),(2,4),(2,6),(2,10),(2,11),(2,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1487_q : Finset ℕ := ([0,2,4,6,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1487_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,10),(0,12),(0,14),(2,4),(2,6),(2,10),(2,12),(2,14),(4,6),(4,10),(4,12),(4,14),(6,10),(6,12),(6,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1488_q : Finset ℕ := ([0,2,4,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1488_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(2,4),(2,7),(2,8),(2,10),(2,13),(4,7),(4,8),(4,10),(4,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1489_q : Finset ℕ := ([0,2,4,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1489_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,8),(0,10),(0,14),(2,4),(2,7),(2,8),(2,10),(2,14),(4,7),(4,8),(4,10),(4,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1490_q : Finset ℕ := ([0,2,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1490_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,8),(0,11),(0,14),(2,4),(2,7),(2,8),(2,11),(2,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1491_q : Finset ℕ := ([0,2,4,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1491_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(2,4),(2,7),(2,9),(2,10),(2,13),(4,7),(4,9),(4,10),(4,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1492_q : Finset ℕ := ([0,2,4,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1492_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,9),(0,10),(0,14),(2,4),(2,7),(2,9),(2,10),(2,14),(4,7),(4,9),(4,10),(4,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1493_q : Finset ℕ := ([0,2,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1493_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,9),(0,11),(0,14),(2,4),(2,7),(2,9),(2,11),(2,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1494_q : Finset ℕ := ([0,2,4,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1494_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,9),(0,12),(0,14),(2,4),(2,7),(2,9),(2,12),(2,14),(4,7),(4,9),(4,12),(4,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1495_q : Finset ℕ := ([0,2,4,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1495_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,10),(0,11),(0,14),(2,4),(2,7),(2,10),(2,11),(2,14),(4,7),(4,10),(4,11),(4,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1496_q : Finset ℕ := ([0,2,4,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1496_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,7),(0,10),(0,12),(0,14),(2,4),(2,7),(2,10),(2,12),(2,14),(4,7),(4,10),(4,12),(4,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1497_q : Finset ℕ := ([0,2,4,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1497_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,8),(0,9),(0,11),(0,14),(2,4),(2,8),(2,9),(2,11),(2,14),(4,8),(4,9),(4,11),(4,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1498_q : Finset ℕ := ([0,2,4,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1498_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,8),(0,10),(0,11),(0,14),(2,4),(2,8),(2,10),(2,11),(2,14),(4,8),(4,10),(4,11),(4,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1499_q : Finset ℕ := ([0,2,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1499_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,5),(0,6),(0,8),(0,11),(0,13),(2,5),(2,6),(2,8),(2,11),(2,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1500_q : Finset ℕ := ([0,2,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1500_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,6),(0,8),(0,11),(0,14),(2,5),(2,6),(2,8),(2,11),(2,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1501_q : Finset ℕ := ([0,2,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1501_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,6),(0,8),(0,12),(0,14),(2,5),(2,6),(2,8),(2,12),(2,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1502_q : Finset ℕ := ([0,2,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1502_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(2,5),(2,6),(2,9),(2,10),(2,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1503_q : Finset ℕ := ([0,2,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1503_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,6),(0,9),(0,10),(0,14),(2,5),(2,6),(2,9),(2,10),(2,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates048
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1504_q : Finset ℕ := ([0,2,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1504_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,6),(0,9),(0,11),(0,14),(2,5),(2,6),(2,9),(2,11),(2,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1505_q : Finset ℕ := ([0,2,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1505_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,7),(0,8),(0,10),(0,14),(2,5),(2,7),(2,8),(2,10),(2,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1506_q : Finset ℕ := ([0,2,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1506_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,7),(0,8),(0,11),(0,14),(2,5),(2,7),(2,8),(2,11),(2,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1507_q : Finset ℕ := ([0,2,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1507_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,7),(0,9),(0,11),(0,14),(2,5),(2,7),(2,9),(2,11),(2,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1508_q : Finset ℕ := ([0,2,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1508_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,5),(0,7),(0,9),(0,12),(0,14),(2,5),(2,7),(2,9),(2,12),(2,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1509_q : Finset ℕ := ([0,2,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1509_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,5),(0,7),(0,10),(0,11),(0,14),(2,5),(2,7),(2,10),(2,11),(2,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1510_q : Finset ℕ := ([0,2,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1510_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,5),(0,8),(0,10),(0,11),(0,14),(2,5),(2,8),(2,10),(2,11),(2,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1511_q : Finset ℕ := ([0,2,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1511_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,6),(0,7),(0,10),(0,11),(0,14),(2,6),(2,7),(2,10),(2,11),(2,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1512_q : Finset ℕ := ([0,3,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1512_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,3),(0,4),(0,7),(0,8),(0,11),(0,14),(3,4),(3,7),(3,8),(3,11),(3,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1513_q : Finset ℕ := ([0,3,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1513_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,3),(0,4),(0,7),(0,9),(0,11),(0,14),(3,4),(3,7),(3,9),(3,11),(3,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1514_q : Finset ℕ := ([0,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1514_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1515_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_1515_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_1516_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_1516_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_1517_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_1517_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_1518_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_1518_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_1519_q : Finset ℕ := ([0,1,2,3,4,5,6,11] : List ℕ).toFinset
noncomputable def certificate_1519_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,11),(1,2),(1,3),(1,4),(1,5),(1,6),(1,11),(2,3),(2,4),(2,5),(2,6),(2,11),(3,4),(3,5),(3,6),(3,11),(4,5),(4,6),(4,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_1520_q : Finset ℕ := ([0,1,2,3,4,5,6,12] : List ℕ).toFinset
noncomputable def certificate_1520_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,12),(1,2),(1,3),(1,4),(1,5),(1,6),(1,12),(2,3),(2,4),(2,5),(2,6),(2,12),(3,4),(3,5),(3,6),(3,12),(4,5),(4,6),(4,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_1521_q : Finset ℕ := ([0,1,2,3,4,5,6,13] : List ℕ).toFinset
noncomputable def certificate_1521_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,13),(1,2),(1,3),(1,4),(1,5),(1,6),(1,13),(2,3),(2,4),(2,5),(2,6),(2,13),(3,4),(3,5),(3,6),(3,13),(4,5),(4,6),(4,13),(5,6),(5,13),(6,13)]

noncomputable def certificate_1522_q : Finset ℕ := ([0,1,2,3,4,5,6,14] : List ℕ).toFinset
noncomputable def certificate_1522_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,14),(1,2),(1,3),(1,4),(1,5),(1,6),(1,14),(2,3),(2,4),(2,5),(2,6),(2,14),(3,4),(3,5),(3,6),(3,14),(4,5),(4,6),(4,14),(5,6),(5,14),(6,14)]

noncomputable def certificate_1523_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_1523_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_1524_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_1524_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_1525_q : Finset ℕ := ([0,1,2,3,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_1525_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,11),(1,2),(1,3),(1,4),(1,5),(1,7),(1,11),(2,3),(2,4),(2,5),(2,7),(2,11),(3,4),(3,5),(3,7),(3,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_1526_q : Finset ℕ := ([0,1,2,3,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_1526_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,12),(1,2),(1,3),(1,4),(1,5),(1,7),(1,12),(2,3),(2,4),(2,5),(2,7),(2,12),(3,4),(3,5),(3,7),(3,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_1527_q : Finset ℕ := ([0,1,2,3,4,5,7,13] : List ℕ).toFinset
noncomputable def certificate_1527_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,13),(1,2),(1,3),(1,4),(1,5),(1,7),(1,13),(2,3),(2,4),(2,5),(2,7),(2,13),(3,4),(3,5),(3,7),(3,13),(4,5),(4,7),(4,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_1528_q : Finset ℕ := ([0,1,2,3,4,5,7,14] : List ℕ).toFinset
noncomputable def certificate_1528_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,14),(1,2),(1,3),(1,4),(1,5),(1,7),(1,14),(2,3),(2,4),(2,5),(2,7),(2,14),(3,4),(3,5),(3,7),(3,14),(4,5),(4,7),(4,14),(5,7),(5,14),(7,14)]

noncomputable def certificate_1529_q : Finset ℕ := ([0,1,2,3,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_1529_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,11),(1,2),(1,3),(1,4),(1,5),(1,8),(1,11),(2,3),(2,4),(2,5),(2,8),(2,11),(3,4),(3,5),(3,8),(3,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_1530_q : Finset ℕ := ([0,1,2,3,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_1530_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,12),(1,2),(1,3),(1,4),(1,5),(1,8),(1,12),(2,3),(2,4),(2,5),(2,8),(2,12),(3,4),(3,5),(3,8),(3,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_1531_q : Finset ℕ := ([0,1,2,3,4,5,8,13] : List ℕ).toFinset
noncomputable def certificate_1531_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,13),(1,2),(1,3),(1,4),(1,5),(1,8),(1,13),(2,3),(2,4),(2,5),(2,8),(2,13),(3,4),(3,5),(3,8),(3,13),(4,5),(4,8),(4,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_1532_q : Finset ℕ := ([0,1,2,3,4,5,8,14] : List ℕ).toFinset
noncomputable def certificate_1532_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,14),(1,2),(1,3),(1,4),(1,5),(1,8),(1,14),(2,3),(2,4),(2,5),(2,8),(2,14),(3,4),(3,5),(3,8),(3,14),(4,5),(4,8),(4,14),(5,8),(5,14),(8,14)]

noncomputable def certificate_1533_q : Finset ℕ := ([0,1,2,3,4,5,9,13] : List ℕ).toFinset
noncomputable def certificate_1533_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,13),(1,2),(1,3),(1,4),(1,5),(1,9),(1,13),(2,3),(2,4),(2,5),(2,9),(2,13),(3,4),(3,5),(3,9),(3,13),(4,5),(4,9),(4,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_1534_q : Finset ℕ := ([0,1,2,3,4,5,9,14] : List ℕ).toFinset
noncomputable def certificate_1534_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,14),(1,2),(1,3),(1,4),(1,5),(1,9),(1,14),(2,3),(2,4),(2,5),(2,9),(2,14),(3,4),(3,5),(3,9),(3,14),(4,5),(4,9),(4,14),(5,9),(5,14),(9,14)]

noncomputable def certificate_1535_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_1535_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates049
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1536_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_1536_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_1537_q : Finset ℕ := ([0,1,2,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_1537_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,11),(1,2),(1,3),(1,4),(1,6),(1,7),(1,11),(2,3),(2,4),(2,6),(2,7),(2,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_1538_q : Finset ℕ := ([0,1,2,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_1538_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,12),(1,2),(1,3),(1,4),(1,6),(1,7),(1,12),(2,3),(2,4),(2,6),(2,7),(2,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_1539_q : Finset ℕ := ([0,1,2,3,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_1539_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,13),(1,2),(1,3),(1,4),(1,6),(1,7),(1,13),(2,3),(2,4),(2,6),(2,7),(2,13),(3,4),(3,6),(3,7),(3,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_1540_q : Finset ℕ := ([0,1,2,3,4,6,7,14] : List ℕ).toFinset
noncomputable def certificate_1540_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,14),(1,2),(1,3),(1,4),(1,6),(1,7),(1,14),(2,3),(2,4),(2,6),(2,7),(2,14),(3,4),(3,6),(3,7),(3,14),(4,6),(4,7),(4,14),(6,7),(6,14),(7,14)]

noncomputable def certificate_1541_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1541_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1542_q : Finset ℕ := ([0,1,2,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1542_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,11),(1,2),(1,3),(1,4),(1,6),(1,8),(1,11),(2,3),(2,4),(2,6),(2,8),(2,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1543_q : Finset ℕ := ([0,1,2,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1543_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,12),(1,2),(1,3),(1,4),(1,6),(1,8),(1,12),(2,3),(2,4),(2,6),(2,8),(2,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1544_q : Finset ℕ := ([0,1,2,3,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1544_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,13),(1,2),(1,3),(1,4),(1,6),(1,8),(1,13),(2,3),(2,4),(2,6),(2,8),(2,13),(3,4),(3,6),(3,8),(3,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1545_q : Finset ℕ := ([0,1,2,3,4,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1545_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,14),(1,2),(1,3),(1,4),(1,6),(1,8),(1,14),(2,3),(2,4),(2,6),(2,8),(2,14),(3,4),(3,6),(3,8),(3,14),(4,6),(4,8),(4,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1546_q : Finset ℕ := ([0,1,2,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_1546_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,11),(1,2),(1,3),(1,4),(1,6),(1,9),(1,11),(2,3),(2,4),(2,6),(2,9),(2,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_1547_q : Finset ℕ := ([0,1,2,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1547_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,12),(1,2),(1,3),(1,4),(1,6),(1,9),(1,12),(2,3),(2,4),(2,6),(2,9),(2,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1548_q : Finset ℕ := ([0,1,2,3,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1548_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,13),(1,2),(1,3),(1,4),(1,6),(1,9),(1,13),(2,3),(2,4),(2,6),(2,9),(2,13),(3,4),(3,6),(3,9),(3,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1549_q : Finset ℕ := ([0,1,2,3,4,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1549_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,14),(1,2),(1,3),(1,4),(1,6),(1,9),(1,14),(2,3),(2,4),(2,6),(2,9),(2,14),(3,4),(3,6),(3,9),(3,14),(4,6),(4,9),(4,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1550_q : Finset ℕ := ([0,1,2,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_1550_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,12),(1,2),(1,3),(1,4),(1,6),(1,10),(1,12),(2,3),(2,4),(2,6),(2,10),(2,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_1551_q : Finset ℕ := ([0,1,2,3,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_1551_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,13),(1,2),(1,3),(1,4),(1,6),(1,10),(1,13),(2,3),(2,4),(2,6),(2,10),(2,13),(3,4),(3,6),(3,10),(3,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_1552_q : Finset ℕ := ([0,1,2,3,4,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1552_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,14),(1,2),(1,3),(1,4),(1,6),(1,10),(1,14),(2,3),(2,4),(2,6),(2,10),(2,14),(3,4),(3,6),(3,10),(3,14),(4,6),(4,10),(4,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1553_q : Finset ℕ := ([0,1,2,3,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_1553_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,13),(1,2),(1,3),(1,4),(1,6),(1,11),(1,13),(2,3),(2,4),(2,6),(2,11),(2,13),(3,4),(3,6),(3,11),(3,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_1554_q : Finset ℕ := ([0,1,2,3,4,6,11,14] : List ℕ).toFinset
noncomputable def certificate_1554_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,14),(1,2),(1,3),(1,4),(1,6),(1,11),(1,14),(2,3),(2,4),(2,6),(2,11),(2,14),(3,4),(3,6),(3,11),(3,14),(4,6),(4,11),(4,14),(6,11),(6,14),(11,14)]

noncomputable def certificate_1555_q : Finset ℕ := ([0,1,2,3,4,6,12,14] : List ℕ).toFinset
noncomputable def certificate_1555_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(0,14),(1,2),(1,3),(1,4),(1,6),(1,12),(1,14),(2,3),(2,4),(2,6),(2,12),(2,14),(3,4),(3,6),(3,12),(3,14),(4,6),(4,12),(4,14),(6,12),(6,14),(12,14)]

noncomputable def certificate_1556_q : Finset ℕ := ([0,1,2,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1556_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,11),(1,2),(1,3),(1,4),(1,7),(1,8),(1,11),(2,3),(2,4),(2,7),(2,8),(2,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1557_q : Finset ℕ := ([0,1,2,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1557_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,12),(1,2),(1,3),(1,4),(1,7),(1,8),(1,12),(2,3),(2,4),(2,7),(2,8),(2,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1558_q : Finset ℕ := ([0,1,2,3,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1558_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,13),(1,2),(1,3),(1,4),(1,7),(1,8),(1,13),(2,3),(2,4),(2,7),(2,8),(2,13),(3,4),(3,7),(3,8),(3,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1559_q : Finset ℕ := ([0,1,2,3,4,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1559_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,14),(1,2),(1,3),(1,4),(1,7),(1,8),(1,14),(2,3),(2,4),(2,7),(2,8),(2,14),(3,4),(3,7),(3,8),(3,14),(4,7),(4,8),(4,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1560_q : Finset ℕ := ([0,1,2,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1560_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,12),(1,2),(1,3),(1,4),(1,7),(1,9),(1,12),(2,3),(2,4),(2,7),(2,9),(2,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1561_q : Finset ℕ := ([0,1,2,3,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1561_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,13),(1,2),(1,3),(1,4),(1,7),(1,9),(1,13),(2,3),(2,4),(2,7),(2,9),(2,13),(3,4),(3,7),(3,9),(3,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1562_q : Finset ℕ := ([0,1,2,3,4,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1562_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,14),(1,2),(1,3),(1,4),(1,7),(1,9),(1,14),(2,3),(2,4),(2,7),(2,9),(2,14),(3,4),(3,7),(3,9),(3,14),(4,7),(4,9),(4,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1563_q : Finset ℕ := ([0,1,2,3,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1563_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,13),(1,2),(1,3),(1,4),(1,7),(1,10),(1,13),(2,3),(2,4),(2,7),(2,10),(2,13),(3,4),(3,7),(3,10),(3,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1564_q : Finset ℕ := ([0,1,2,3,4,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1564_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,14),(1,2),(1,3),(1,4),(1,7),(1,10),(1,14),(2,3),(2,4),(2,7),(2,10),(2,14),(3,4),(3,7),(3,10),(3,14),(4,7),(4,10),(4,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1565_q : Finset ℕ := ([0,1,2,3,4,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1565_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(0,14),(1,2),(1,3),(1,4),(1,7),(1,11),(1,14),(2,3),(2,4),(2,7),(2,11),(2,14),(3,4),(3,7),(3,11),(3,14),(4,7),(4,11),(4,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1566_q : Finset ℕ := ([0,1,2,3,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1566_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,13),(1,2),(1,3),(1,4),(1,8),(1,9),(1,13),(2,3),(2,4),(2,8),(2,9),(2,13),(3,4),(3,8),(3,9),(3,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1567_q : Finset ℕ := ([0,1,2,3,4,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1567_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,14),(1,2),(1,3),(1,4),(1,8),(1,9),(1,14),(2,3),(2,4),(2,8),(2,9),(2,14),(3,4),(3,8),(3,9),(3,14),(4,8),(4,9),(4,14),(8,9),(8,14),(9,14)]

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

noncomputable def certificate_1568_q : Finset ℕ := ([0,1,2,3,4,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1568_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,10),(0,14),(1,2),(1,3),(1,4),(1,8),(1,10),(1,14),(2,3),(2,4),(2,8),(2,10),(2,14),(3,4),(3,8),(3,10),(3,14),(4,8),(4,10),(4,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1569_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1569_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1570_q : Finset ℕ := ([0,1,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1570_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(1,2),(1,3),(1,5),(1,6),(1,8),(1,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1571_q : Finset ℕ := ([0,1,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1571_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(1,2),(1,3),(1,5),(1,6),(1,8),(1,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1572_q : Finset ℕ := ([0,1,2,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1572_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(1,2),(1,3),(1,5),(1,6),(1,8),(1,13),(2,3),(2,5),(2,6),(2,8),(2,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1573_q : Finset ℕ := ([0,1,2,3,5,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1573_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,14),(1,2),(1,3),(1,5),(1,6),(1,8),(1,14),(2,3),(2,5),(2,6),(2,8),(2,14),(3,5),(3,6),(3,8),(3,14),(5,6),(5,8),(5,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1574_q : Finset ℕ := ([0,1,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1574_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(1,2),(1,3),(1,5),(1,6),(1,9),(1,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1575_q : Finset ℕ := ([0,1,2,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1575_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(1,2),(1,3),(1,5),(1,6),(1,9),(1,13),(2,3),(2,5),(2,6),(2,9),(2,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1576_q : Finset ℕ := ([0,1,2,3,5,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1576_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,14),(1,2),(1,3),(1,5),(1,6),(1,9),(1,14),(2,3),(2,5),(2,6),(2,9),(2,14),(3,5),(3,6),(3,9),(3,14),(5,6),(5,9),(5,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1577_q : Finset ℕ := ([0,1,2,3,5,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1577_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(0,14),(1,2),(1,3),(1,5),(1,6),(1,10),(1,14),(2,3),(2,5),(2,6),(2,10),(2,14),(3,5),(3,6),(3,10),(3,14),(5,6),(5,10),(5,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1578_q : Finset ℕ := ([0,1,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1578_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(1,2),(1,3),(1,5),(1,7),(1,8),(1,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1579_q : Finset ℕ := ([0,1,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1579_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(1,2),(1,3),(1,5),(1,7),(1,8),(1,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1580_q : Finset ℕ := ([0,1,2,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1580_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,13),(1,2),(1,3),(1,5),(1,7),(1,8),(1,13),(2,3),(2,5),(2,7),(2,8),(2,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1581_q : Finset ℕ := ([0,1,2,3,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1581_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,14),(1,2),(1,3),(1,5),(1,7),(1,8),(1,14),(2,3),(2,5),(2,7),(2,8),(2,14),(3,5),(3,7),(3,8),(3,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1582_q : Finset ℕ := ([0,1,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1582_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(1,2),(1,3),(1,5),(1,7),(1,9),(1,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1583_q : Finset ℕ := ([0,1,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1583_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(1,2),(1,3),(1,5),(1,7),(1,9),(1,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1584_q : Finset ℕ := ([0,1,2,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1584_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(1,2),(1,3),(1,5),(1,7),(1,9),(1,13),(2,3),(2,5),(2,7),(2,9),(2,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1585_q : Finset ℕ := ([0,1,2,3,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1585_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,14),(1,2),(1,3),(1,5),(1,7),(1,9),(1,14),(2,3),(2,5),(2,7),(2,9),(2,14),(3,5),(3,7),(3,9),(3,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1586_q : Finset ℕ := ([0,1,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1586_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(1,2),(1,3),(1,5),(1,7),(1,10),(1,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1587_q : Finset ℕ := ([0,1,2,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1587_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(1,2),(1,3),(1,5),(1,7),(1,10),(1,13),(2,3),(2,5),(2,7),(2,10),(2,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1588_q : Finset ℕ := ([0,1,2,3,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1588_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,14),(1,2),(1,3),(1,5),(1,7),(1,10),(1,14),(2,3),(2,5),(2,7),(2,10),(2,14),(3,5),(3,7),(3,10),(3,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1589_q : Finset ℕ := ([0,1,2,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1589_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(1,2),(1,3),(1,5),(1,7),(1,11),(1,13),(2,3),(2,5),(2,7),(2,11),(2,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1590_q : Finset ℕ := ([0,1,2,3,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1590_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,14),(1,2),(1,3),(1,5),(1,7),(1,11),(1,14),(2,3),(2,5),(2,7),(2,11),(2,14),(3,5),(3,7),(3,11),(3,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1591_q : Finset ℕ := ([0,1,2,3,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1591_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(0,14),(1,2),(1,3),(1,5),(1,7),(1,12),(1,14),(2,3),(2,5),(2,7),(2,12),(2,14),(3,5),(3,7),(3,12),(3,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1592_q : Finset ℕ := ([0,1,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1592_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(1,2),(1,3),(1,5),(1,8),(1,9),(1,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1593_q : Finset ℕ := ([0,1,2,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1593_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,13),(1,2),(1,3),(1,5),(1,8),(1,9),(1,13),(2,3),(2,5),(2,8),(2,9),(2,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1594_q : Finset ℕ := ([0,1,2,3,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1594_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,14),(1,2),(1,3),(1,5),(1,8),(1,9),(1,14),(2,3),(2,5),(2,8),(2,9),(2,14),(3,5),(3,8),(3,9),(3,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1595_q : Finset ℕ := ([0,1,2,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1595_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(1,2),(1,3),(1,5),(1,8),(1,10),(1,13),(2,3),(2,5),(2,8),(2,10),(2,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1596_q : Finset ℕ := ([0,1,2,3,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1596_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,14),(1,2),(1,3),(1,5),(1,8),(1,10),(1,14),(2,3),(2,5),(2,8),(2,10),(2,14),(3,5),(3,8),(3,10),(3,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1597_q : Finset ℕ := ([0,1,2,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1597_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(1,2),(1,3),(1,5),(1,8),(1,11),(1,13),(2,3),(2,5),(2,8),(2,11),(2,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1598_q : Finset ℕ := ([0,1,2,3,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1598_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,14),(1,2),(1,3),(1,5),(1,8),(1,11),(1,14),(2,3),(2,5),(2,8),(2,11),(2,14),(3,5),(3,8),(3,11),(3,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1599_q : Finset ℕ := ([0,1,2,3,5,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1599_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(0,14),(1,2),(1,3),(1,5),(1,8),(1,12),(1,14),(2,3),(2,5),(2,8),(2,12),(2,14),(3,5),(3,8),(3,12),(3,14),(5,8),(5,12),(5,14),(8,12),(8,14),(12,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates051
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1600_q : Finset ℕ := ([0,1,2,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1600_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(1,2),(1,3),(1,5),(1,9),(1,10),(1,13),(2,3),(2,5),(2,9),(2,10),(2,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1601_q : Finset ℕ := ([0,1,2,3,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1601_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,14),(1,2),(1,3),(1,5),(1,9),(1,10),(1,14),(2,3),(2,5),(2,9),(2,10),(2,14),(3,5),(3,9),(3,10),(3,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1602_q : Finset ℕ := ([0,1,2,3,5,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1602_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(0,14),(1,2),(1,3),(1,5),(1,9),(1,11),(1,14),(2,3),(2,5),(2,9),(2,11),(2,14),(3,5),(3,9),(3,11),(3,14),(5,9),(5,11),(5,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1603_q : Finset ℕ := ([0,1,2,3,5,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1603_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,10),(0,11),(0,14),(1,2),(1,3),(1,5),(1,10),(1,11),(1,14),(2,3),(2,5),(2,10),(2,11),(2,14),(3,5),(3,10),(3,11),(3,14),(5,10),(5,11),(5,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1604_q : Finset ℕ := ([0,1,2,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1604_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(1,2),(1,3),(1,6),(1,7),(1,10),(1,13),(2,3),(2,6),(2,7),(2,10),(2,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1605_q : Finset ℕ := ([0,1,2,3,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1605_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,14),(1,2),(1,3),(1,6),(1,7),(1,10),(1,14),(2,3),(2,6),(2,7),(2,10),(2,14),(3,6),(3,7),(3,10),(3,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1606_q : Finset ℕ := ([0,1,2,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1606_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(1,2),(1,3),(1,6),(1,8),(1,10),(1,13),(2,3),(2,6),(2,8),(2,10),(2,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1607_q : Finset ℕ := ([0,1,2,3,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1607_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,14),(1,2),(1,3),(1,6),(1,8),(1,10),(1,14),(2,3),(2,6),(2,8),(2,10),(2,14),(3,6),(3,8),(3,10),(3,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1608_q : Finset ℕ := ([0,1,2,3,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1608_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(0,14),(1,2),(1,3),(1,6),(1,8),(1,11),(1,14),(2,3),(2,6),(2,8),(2,11),(2,14),(3,6),(3,8),(3,11),(3,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1609_q : Finset ℕ := ([0,1,2,3,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1609_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,9),(0,10),(0,14),(1,2),(1,3),(1,6),(1,9),(1,10),(1,14),(2,3),(2,6),(2,9),(2,10),(2,14),(3,6),(3,9),(3,10),(3,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1610_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset
noncomputable def certificate_1610_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_1611_q : Finset ℕ := ([0,1,2,4,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1611_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,11),(1,2),(1,4),(1,5),(1,7),(1,8),(1,11),(2,4),(2,5),(2,7),(2,8),(2,11),(4,5),(4,7),(4,8),(4,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1612_q : Finset ℕ := ([0,1,2,4,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1612_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,12),(1,2),(1,4),(1,5),(1,7),(1,8),(1,12),(2,4),(2,5),(2,7),(2,8),(2,12),(4,5),(4,7),(4,8),(4,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1613_q : Finset ℕ := ([0,1,2,4,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1613_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,13),(1,2),(1,4),(1,5),(1,7),(1,8),(1,13),(2,4),(2,5),(2,7),(2,8),(2,13),(4,5),(4,7),(4,8),(4,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1614_q : Finset ℕ := ([0,1,2,4,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1614_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,14),(1,2),(1,4),(1,5),(1,7),(1,8),(1,14),(2,4),(2,5),(2,7),(2,8),(2,14),(4,5),(4,7),(4,8),(4,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1615_q : Finset ℕ := ([0,1,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1615_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(1,2),(1,4),(1,5),(1,7),(1,9),(1,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1616_q : Finset ℕ := ([0,1,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1616_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(1,2),(1,4),(1,5),(1,7),(1,9),(1,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1617_q : Finset ℕ := ([0,1,2,4,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1617_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(1,2),(1,4),(1,5),(1,7),(1,9),(1,13),(2,4),(2,5),(2,7),(2,9),(2,13),(4,5),(4,7),(4,9),(4,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1618_q : Finset ℕ := ([0,1,2,4,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1618_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,14),(1,2),(1,4),(1,5),(1,7),(1,9),(1,14),(2,4),(2,5),(2,7),(2,9),(2,14),(4,5),(4,7),(4,9),(4,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1619_q : Finset ℕ := ([0,1,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1619_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(1,2),(1,4),(1,5),(1,7),(1,10),(1,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1620_q : Finset ℕ := ([0,1,2,4,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1620_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(1,2),(1,4),(1,5),(1,7),(1,10),(1,13),(2,4),(2,5),(2,7),(2,10),(2,13),(4,5),(4,7),(4,10),(4,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1621_q : Finset ℕ := ([0,1,2,4,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1621_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,14),(1,2),(1,4),(1,5),(1,7),(1,10),(1,14),(2,4),(2,5),(2,7),(2,10),(2,14),(4,5),(4,7),(4,10),(4,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1622_q : Finset ℕ := ([0,1,2,4,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1622_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(1,2),(1,4),(1,5),(1,7),(1,11),(1,13),(2,4),(2,5),(2,7),(2,11),(2,13),(4,5),(4,7),(4,11),(4,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1623_q : Finset ℕ := ([0,1,2,4,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1623_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,14),(1,2),(1,4),(1,5),(1,7),(1,11),(1,14),(2,4),(2,5),(2,7),(2,11),(2,14),(4,5),(4,7),(4,11),(4,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1624_q : Finset ℕ := ([0,1,2,4,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1624_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(0,14),(1,2),(1,4),(1,5),(1,7),(1,12),(1,14),(2,4),(2,5),(2,7),(2,12),(2,14),(4,5),(4,7),(4,12),(4,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1625_q : Finset ℕ := ([0,1,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1625_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(1,2),(1,4),(1,5),(1,8),(1,9),(1,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1626_q : Finset ℕ := ([0,1,2,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1626_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,13),(1,2),(1,4),(1,5),(1,8),(1,9),(1,13),(2,4),(2,5),(2,8),(2,9),(2,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1627_q : Finset ℕ := ([0,1,2,4,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1627_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,14),(1,2),(1,4),(1,5),(1,8),(1,9),(1,14),(2,4),(2,5),(2,8),(2,9),(2,14),(4,5),(4,8),(4,9),(4,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1628_q : Finset ℕ := ([0,1,2,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1628_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(1,2),(1,4),(1,5),(1,8),(1,10),(1,13),(2,4),(2,5),(2,8),(2,10),(2,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1629_q : Finset ℕ := ([0,1,2,4,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1629_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,14),(1,2),(1,4),(1,5),(1,8),(1,10),(1,14),(2,4),(2,5),(2,8),(2,10),(2,14),(4,5),(4,8),(4,10),(4,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1630_q : Finset ℕ := ([0,1,2,4,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1630_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(0,14),(1,2),(1,4),(1,5),(1,8),(1,11),(1,14),(2,4),(2,5),(2,8),(2,11),(2,14),(4,5),(4,8),(4,11),(4,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1631_q : Finset ℕ := ([0,1,2,4,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1631_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,9),(0,10),(0,14),(1,2),(1,4),(1,5),(1,9),(1,10),(1,14),(2,4),(2,5),(2,9),(2,10),(2,14),(4,5),(4,9),(4,10),(4,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates052
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1632_q : Finset ℕ := ([0,1,2,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1632_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(1,2),(1,4),(1,6),(1,7),(1,9),(1,11),(2,4),(2,6),(2,7),(2,9),(2,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1633_q : Finset ℕ := ([0,1,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1633_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(1,2),(1,4),(1,6),(1,7),(1,9),(1,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1634_q : Finset ℕ := ([0,1,2,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1634_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(1,2),(1,4),(1,6),(1,7),(1,9),(1,13),(2,4),(2,6),(2,7),(2,9),(2,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1635_q : Finset ℕ := ([0,1,2,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1635_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,14),(1,2),(1,4),(1,6),(1,7),(1,9),(1,14),(2,4),(2,6),(2,7),(2,9),(2,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1636_q : Finset ℕ := ([0,1,2,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1636_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(1,2),(1,4),(1,6),(1,7),(1,10),(1,13),(2,4),(2,6),(2,7),(2,10),(2,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1637_q : Finset ℕ := ([0,1,2,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1637_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,14),(1,2),(1,4),(1,6),(1,7),(1,10),(1,14),(2,4),(2,6),(2,7),(2,10),(2,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1638_q : Finset ℕ := ([0,1,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1638_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(1,2),(1,4),(1,6),(1,8),(1,9),(1,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1639_q : Finset ℕ := ([0,1,2,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1639_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,13),(1,2),(1,4),(1,6),(1,8),(1,9),(1,13),(2,4),(2,6),(2,8),(2,9),(2,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1640_q : Finset ℕ := ([0,1,2,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1640_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,14),(1,2),(1,4),(1,6),(1,8),(1,9),(1,14),(2,4),(2,6),(2,8),(2,9),(2,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1641_q : Finset ℕ := ([0,1,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1641_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(1,2),(1,4),(1,6),(1,8),(1,10),(1,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1642_q : Finset ℕ := ([0,1,2,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1642_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(1,2),(1,4),(1,6),(1,8),(1,10),(1,13),(2,4),(2,6),(2,8),(2,10),(2,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1643_q : Finset ℕ := ([0,1,2,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1643_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,14),(1,2),(1,4),(1,6),(1,8),(1,10),(1,14),(2,4),(2,6),(2,8),(2,10),(2,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1644_q : Finset ℕ := ([0,1,2,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1644_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(1,2),(1,4),(1,6),(1,8),(1,11),(1,13),(2,4),(2,6),(2,8),(2,11),(2,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1645_q : Finset ℕ := ([0,1,2,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1645_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,14),(1,2),(1,4),(1,6),(1,8),(1,11),(1,14),(2,4),(2,6),(2,8),(2,11),(2,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1646_q : Finset ℕ := ([0,1,2,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1646_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(0,14),(1,2),(1,4),(1,6),(1,8),(1,12),(1,14),(2,4),(2,6),(2,8),(2,12),(2,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1647_q : Finset ℕ := ([0,1,2,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1647_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(1,2),(1,4),(1,6),(1,9),(1,10),(1,13),(2,4),(2,6),(2,9),(2,10),(2,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1648_q : Finset ℕ := ([0,1,2,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1648_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,14),(1,2),(1,4),(1,6),(1,9),(1,10),(1,14),(2,4),(2,6),(2,9),(2,10),(2,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1649_q : Finset ℕ := ([0,1,2,4,6,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1649_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(1,2),(1,4),(1,6),(1,9),(1,11),(1,13),(2,4),(2,6),(2,9),(2,11),(2,13),(4,6),(4,9),(4,11),(4,13),(6,9),(6,11),(6,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1650_q : Finset ℕ := ([0,1,2,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1650_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,14),(1,2),(1,4),(1,6),(1,9),(1,11),(1,14),(2,4),(2,6),(2,9),(2,11),(2,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1651_q : Finset ℕ := ([0,1,2,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1651_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(0,14),(1,2),(1,4),(1,6),(1,9),(1,12),(1,14),(2,4),(2,6),(2,9),(2,12),(2,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1652_q : Finset ℕ := ([0,1,2,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1652_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,14),(1,2),(1,4),(1,6),(1,10),(1,11),(1,14),(2,4),(2,6),(2,10),(2,11),(2,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1653_q : Finset ℕ := ([0,1,2,4,6,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1653_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(0,14),(1,2),(1,4),(1,6),(1,10),(1,12),(1,14),(2,4),(2,6),(2,10),(2,12),(2,14),(4,6),(4,10),(4,12),(4,14),(6,10),(6,12),(6,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1654_q : Finset ℕ := ([0,1,2,4,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1654_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(1,2),(1,4),(1,7),(1,8),(1,10),(1,13),(2,4),(2,7),(2,8),(2,10),(2,13),(4,7),(4,8),(4,10),(4,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1655_q : Finset ℕ := ([0,1,2,4,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1655_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,14),(1,2),(1,4),(1,7),(1,8),(1,10),(1,14),(2,4),(2,7),(2,8),(2,10),(2,14),(4,7),(4,8),(4,10),(4,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1656_q : Finset ℕ := ([0,1,2,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1656_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(0,14),(1,2),(1,4),(1,7),(1,8),(1,11),(1,14),(2,4),(2,7),(2,8),(2,11),(2,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1657_q : Finset ℕ := ([0,1,2,4,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1657_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(1,2),(1,4),(1,7),(1,9),(1,10),(1,13),(2,4),(2,7),(2,9),(2,10),(2,13),(4,7),(4,9),(4,10),(4,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1658_q : Finset ℕ := ([0,1,2,4,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1658_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,14),(1,2),(1,4),(1,7),(1,9),(1,10),(1,14),(2,4),(2,7),(2,9),(2,10),(2,14),(4,7),(4,9),(4,10),(4,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1659_q : Finset ℕ := ([0,1,2,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1659_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,11),(0,14),(1,2),(1,4),(1,7),(1,9),(1,11),(1,14),(2,4),(2,7),(2,9),(2,11),(2,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1660_q : Finset ℕ := ([0,1,2,4,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1660_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(0,14),(1,2),(1,4),(1,7),(1,9),(1,12),(1,14),(2,4),(2,7),(2,9),(2,12),(2,14),(4,7),(4,9),(4,12),(4,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1661_q : Finset ℕ := ([0,1,2,4,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1661_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,10),(0,11),(0,14),(1,2),(1,4),(1,7),(1,10),(1,11),(1,14),(2,4),(2,7),(2,10),(2,11),(2,14),(4,7),(4,10),(4,11),(4,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1662_q : Finset ℕ := ([0,1,2,4,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1662_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,10),(0,11),(0,14),(1,2),(1,4),(1,8),(1,10),(1,11),(1,14),(2,4),(2,8),(2,10),(2,11),(2,14),(4,8),(4,10),(4,11),(4,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1663_q : Finset ℕ := ([0,1,2,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1663_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(1,2),(1,5),(1,6),(1,9),(1,10),(1,13),(2,5),(2,6),(2,9),(2,10),(2,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates053
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1664_q : Finset ℕ := ([0,1,2,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1664_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,14),(1,2),(1,5),(1,6),(1,9),(1,10),(1,14),(2,5),(2,6),(2,9),(2,10),(2,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

end CycleClique

end OAI
end


