-- Prove2me | Definitions.Def_OAIQ107D003
-- name    : OAIQ107D003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:38:16.966169+00:00
-- url     : https://prove2.me/theorems/acdff63c-fcc2-4c6a-8058-ecea005e72b9
-- title:
--   Definitions bundle OAIQ107D003 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 910 declarations of OpenAI's Lean: 910 definitions. The definitions and types are `OAI.CycleClique.certificate_1665_edges`, `OAI.CycleClique.certificate_1665_q`, `OAI.CycleClique.certificate_1666_edges`, `OAI.CycleClique.certificate_1666_q`, `OAI.CycleClique.certificate_1667_edges`, `OAI.CycleClique.certificate_1667_q`, `OAI.CycleClique.certificate_1668_edges`, `OAI.CycleClique.certificate_1668_q`, `OAI.CycleClique.certificate_1669_edges`, `OAI.CycleClique.certificate_1669_q`, `OAI.CycleClique.certificate_166_edges`, `OAI.CycleClique.certificate_166_q`, `OAI.CycleClique.certificate_1670_edges`, `OAI.CycleClique.certificate_1670_q`, `OAI.CycleClique.certificate_1671_edges`, `OAI.CycleClique.certificate_1671_q`, `OAI.CycleClique.certificate_1672_edges`, `OAI.CycleClique.certificate_1672_q`, `OAI.CycleClique.certificate_1673_edges`, `OAI.CycleClique.certificate_1673_q`, `OAI.CycleClique.certificate_1674_edges`, `OAI.CycleClique.certificate_1674_q`, `OAI.CycleClique.certificate_1675_edges`, `OAI.CycleClique.certificate_1675_q`, `OAI.CycleClique.certificate_1676_edges`, `OAI.CycleClique.certificate_1676_q`, `OAI.CycleClique.certificate_1677_edges`, `OAI.CycleClique.certificate_1677_q`, `OAI.CycleClique.certificate_1678_edges`, `OAI.CycleClique.certificate_1678_q`, `OAI.CycleClique.certificate_1679_edges`, `OAI.CycleClique.certificate_1679_q`, `OAI.CycleClique.certificate_167_edges`, `OAI.CycleClique.certificate_167_q`, `OAI.CycleClique.certificate_1680_edges`, `OAI.CycleClique.certificate_1680_q`, `OAI.CycleClique.certificate_1681_edges`, `OAI.CycleClique.certificate_1681_q`, `OAI.CycleClique.certificate_1682_edges`, `OAI.CycleClique.certificate_1682_q` and 870 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates006`, `Ramsey_CycleClique_Certificates007`, `Ramsey_CycleClique_Certificates053`, `Ramsey_CycleClique_Certificates054`, `Ramsey_CycleClique_Certificates055`, `Ramsey_CycleClique_Certificates056`, `Ramsey_CycleClique_Certificates057`, `Ramsey_CycleClique_Certificates058`, `Ramsey_CycleClique_Certificates059`, `Ramsey_CycleClique_Certificates060`, `Ramsey_CycleClique_Certificates061`, `Ramsey_CycleClique_Certificates062`, `Ramsey_CycleClique_Certificates063`, `Ramsey_CycleClique_Certificates064`, `Ramsey_CycleClique_Certificates065`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D040`, `OAIQ107D043`, `OAIQ107D045`, `OAIQ107D047`, `OAIQ107D051`, `OAIQ107D052` and `OAIQ107D054`.
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

noncomputable def certificate_1_q : Finset ℕ := ([0,1,3] : List ℕ).toFinset

noncomputable def certificate_1_edges : List (ℕ × ℕ) := [(1,2),(2,3),(0,1),(0,3),(1,3)]

noncomputable def certificate_1_E : List (ℕ × ℕ) := certificate_1_edges

noncomputable def certificate_1_part_1_E : List (ℕ × ℕ) := certificate_1_E

noncomputable def certificate_16_q : Finset ℕ := ([0,1,3,5] : List ℕ).toFinset

noncomputable def certificate_16_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,3),(0,5),(1,3),(1,5),(3,5)]

noncomputable def certificate_16_E : List (ℕ × ℕ) := certificate_16_edges

noncomputable def certificate_16_part_1_E : List (ℕ × ℕ) := certificate_16_E

noncomputable def certificate_16_part_2_E : List (ℕ × ℕ) := certificate_16_part_1_E

noncomputable def certificate_17_q : Finset ℕ := ([0,2,3,5] : List ℕ).toFinset
noncomputable def certificate_17_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(0,2),(0,3),(0,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_18_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_18_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_19_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_19_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_20_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset

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

noncomputable def certificate_166_q : Finset ℕ := ([0,1,4,5,8] : List ℕ).toFinset
noncomputable def certificate_166_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,4),(0,5),(0,8),(1,4),(1,5),(1,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_167_q : Finset ℕ := ([0,1,4,5,9] : List ℕ).toFinset
noncomputable def certificate_167_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,4),(0,5),(0,9),(1,4),(1,5),(1,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_168_q : Finset ℕ := ([0,1,4,6,9] : List ℕ).toFinset
noncomputable def certificate_168_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,4),(0,6),(0,9),(1,4),(1,6),(1,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_169_q : Finset ℕ := ([0,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_169_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(0,2),(0,3),(0,5),(0,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_170_q : Finset ℕ := ([0,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_170_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,3),(0,5),(0,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_171_q : Finset ℕ := ([0,2,3,5,9] : List ℕ).toFinset
noncomputable def certificate_171_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,9),(2,3),(2,5),(2,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_172_q : Finset ℕ := ([0,2,3,6,9] : List ℕ).toFinset
noncomputable def certificate_172_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,6),(0,9),(2,3),(2,6),(2,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_173_q : Finset ℕ := ([0,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_173_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(0,2),(0,4),(0,5),(0,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_174_q : Finset ℕ := ([0,2,4,5,9] : List ℕ).toFinset
noncomputable def certificate_174_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,5),(0,9),(2,4),(2,5),(2,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_175_q : Finset ℕ := ([0,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_175_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,4),(0,6),(0,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_176_q : Finset ℕ := ([0,2,4,6,9] : List ℕ).toFinset
noncomputable def certificate_176_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,6),(0,9),(2,4),(2,6),(2,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_177_q : Finset ℕ := ([0,2,4,7,9] : List ℕ).toFinset
noncomputable def certificate_177_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,7),(0,9),(2,4),(2,7),(2,9),(4,7),(4,9),(7,9)]

noncomputable def certificate_178_q : Finset ℕ := ([0,2,5,6,9] : List ℕ).toFinset
noncomputable def certificate_178_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,2),(0,5),(0,6),(0,9),(2,5),(2,6),(2,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_179_q : Finset ℕ := ([0,1,2,3,4,5] : List ℕ).toFinset
noncomputable def certificate_179_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_180_q : Finset ℕ := ([0,1,2,3,4,6] : List ℕ).toFinset
noncomputable def certificate_180_edges : List (ℕ × ℕ) := [(4,5),(5,6),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_181_q : Finset ℕ := ([0,1,2,3,4,7] : List ℕ).toFinset
noncomputable def certificate_181_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,7),(1,2),(1,3),(1,4),(1,7),(2,3),(2,4),(2,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_182_q : Finset ℕ := ([0,1,2,3,4,8] : List ℕ).toFinset
noncomputable def certificate_182_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,8),(1,2),(1,3),(1,4),(1,8),(2,3),(2,4),(2,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_183_q : Finset ℕ := ([0,1,2,3,4,9] : List ℕ).toFinset

noncomputable def certificate_183_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,9),(1,2),(1,3),(1,4),(1,9),(2,3),(2,4),(2,9),(3,4),(3,9),(4,9)]

noncomputable def certificate_183_E : List (ℕ × ℕ) := certificate_183_edges

noncomputable def certificate_183_part_1_E : List (ℕ × ℕ) := certificate_183_E

noncomputable def certificate_183_part_2_E : List (ℕ × ℕ) := certificate_183_part_1_E

noncomputable def certificate_183_part_3_E : List (ℕ × ℕ) := certificate_183_part_2_E

noncomputable def certificate_183_part_4_E : List (ℕ × ℕ) := certificate_183_part_3_E

noncomputable def certificate_183_part_5_E : List (ℕ × ℕ) := certificate_183_part_4_E

noncomputable def certificate_183_part_7_E : List (ℕ × ℕ) := certificate_183_part_5_E

noncomputable def certificate_183_part_11_E : List (ℕ × ℕ) := certificate_183_part_7_E

noncomputable def certificate_183_part_19_E : List (ℕ × ℕ) := certificate_183_part_11_E

noncomputable def certificate_183_part_21_E : List (ℕ × ℕ) := certificate_183_part_19_E

noncomputable def certificate_183_part_25_E : List (ℕ × ℕ) := certificate_183_part_21_E

noncomputable def certificate_184_q : Finset ℕ := ([0,1,2,3,5,7] : List ℕ).toFinset
noncomputable def certificate_184_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,5),(0,7),(1,2),(1,3),(1,5),(1,7),(2,3),(2,5),(2,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_185_q : Finset ℕ := ([0,1,2,3,5,8] : List ℕ).toFinset
noncomputable def certificate_185_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,8),(1,2),(1,3),(1,5),(1,8),(2,3),(2,5),(2,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_186_q : Finset ℕ := ([0,1,2,3,5,9] : List ℕ).toFinset
noncomputable def certificate_186_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,9),(1,2),(1,3),(1,5),(1,9),(2,3),(2,5),(2,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_187_q : Finset ℕ := ([0,1,2,3,6,9] : List ℕ).toFinset
noncomputable def certificate_187_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,6),(0,9),(1,2),(1,3),(1,6),(1,9),(2,3),(2,6),(2,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_188_q : Finset ℕ := ([0,1,2,4,5,7] : List ℕ).toFinset
noncomputable def certificate_188_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(0,1),(0,2),(0,4),(0,5),(0,7),(1,2),(1,4),(1,5),(1,7),(2,4),(2,5),(2,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_189_q : Finset ℕ := ([0,1,2,4,5,8] : List ℕ).toFinset
noncomputable def certificate_189_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,5),(0,8),(1,2),(1,4),(1,5),(1,8),(2,4),(2,5),(2,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_190_q : Finset ℕ := ([0,1,2,4,5,9] : List ℕ).toFinset
noncomputable def certificate_190_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,9),(1,2),(1,4),(1,5),(1,9),(2,4),(2,5),(2,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_191_q : Finset ℕ := ([0,1,2,4,6,8] : List ℕ).toFinset
noncomputable def certificate_191_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,6),(0,8),(1,2),(1,4),(1,6),(1,8),(2,4),(2,6),(2,8),(4,6),(4,8),(6,8)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates007
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_192_q : Finset ℕ := ([0,1,2,4,6,9] : List ℕ).toFinset
noncomputable def certificate_192_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,6),(0,9),(1,2),(1,4),(1,6),(1,9),(2,4),(2,6),(2,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_193_q : Finset ℕ := ([0,1,2,4,7,9] : List ℕ).toFinset
noncomputable def certificate_193_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,7),(0,9),(1,2),(1,4),(1,7),(1,9),(2,4),(2,7),(2,9),(4,7),(4,9),(7,9)]

noncomputable def certificate_194_q : Finset ℕ := ([0,1,2,5,6,9] : List ℕ).toFinset
noncomputable def certificate_194_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,5),(0,6),(0,9),(1,2),(1,5),(1,6),(1,9),(2,5),(2,6),(2,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_195_q : Finset ℕ := ([0,1,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_195_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,6),(0,8),(1,3),(1,4),(1,6),(1,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_196_q : Finset ℕ := ([0,1,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_196_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,9),(1,3),(1,4),(1,6),(1,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_197_q : Finset ℕ := ([0,1,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_197_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,6),(0,9),(1,3),(1,5),(1,6),(1,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_198_q : Finset ℕ := ([0,1,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_198_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,7),(0,9),(1,3),(1,5),(1,7),(1,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_199_q : Finset ℕ := ([0,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_199_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(0,2),(0,3),(0,5),(0,6),(0,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_200_q : Finset ℕ := ([0,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_200_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,6),(0,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_201_q : Finset ℕ := ([0,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_201_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,2),(0,3),(0,5),(0,7),(0,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_202_q : Finset ℕ := ([0,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_202_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,2),(0,4),(0,5),(0,7),(0,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_203_q : Finset ℕ := ([0,1,2,3,4,5,6] : List ℕ).toFinset
noncomputable def certificate_203_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

noncomputable def certificate_204_q : Finset ℕ := ([0,1,2,3,4,5,7] : List ℕ).toFinset
noncomputable def certificate_204_edges : List (ℕ × ℕ) := [(5,6),(6,7),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(1,2),(1,3),(1,4),(1,5),(1,7),(2,3),(2,4),(2,5),(2,7),(3,4),(3,5),(3,7),(4,5),(4,7),(5,7)]

noncomputable def certificate_205_q : Finset ℕ := ([0,1,2,3,4,5,8] : List ℕ).toFinset
noncomputable def certificate_205_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(1,2),(1,3),(1,4),(1,5),(1,8),(2,3),(2,4),(2,5),(2,8),(3,4),(3,5),(3,8),(4,5),(4,8),(5,8)]

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

noncomputable def certificate_1665_q : Finset ℕ := ([0,1,2,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1665_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,11),(0,14),(1,2),(1,5),(1,6),(1,9),(1,11),(1,14),(2,5),(2,6),(2,9),(2,11),(2,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1666_q : Finset ℕ := ([0,1,2,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1666_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,7),(0,9),(0,11),(0,14),(1,2),(1,5),(1,7),(1,9),(1,11),(1,14),(2,5),(2,7),(2,9),(2,11),(2,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1667_q : Finset ℕ := ([0,1,3,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1667_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,11),(1,3),(1,4),(1,6),(1,7),(1,9),(1,11),(3,4),(3,6),(3,7),(3,9),(3,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1668_q : Finset ℕ := ([0,1,3,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1668_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,12),(1,3),(1,4),(1,6),(1,7),(1,9),(1,12),(3,4),(3,6),(3,7),(3,9),(3,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1669_q : Finset ℕ := ([0,1,3,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1669_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,13),(1,3),(1,4),(1,6),(1,7),(1,9),(1,13),(3,4),(3,6),(3,7),(3,9),(3,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1670_q : Finset ℕ := ([0,1,3,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1670_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,14),(1,3),(1,4),(1,6),(1,7),(1,9),(1,14),(3,4),(3,6),(3,7),(3,9),(3,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1671_q : Finset ℕ := ([0,1,3,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1671_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,13),(1,3),(1,4),(1,6),(1,7),(1,10),(1,13),(3,4),(3,6),(3,7),(3,10),(3,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1672_q : Finset ℕ := ([0,1,3,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1672_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,14),(1,3),(1,4),(1,6),(1,7),(1,10),(1,14),(3,4),(3,6),(3,7),(3,10),(3,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1673_q : Finset ℕ := ([0,1,3,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1673_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,12),(1,3),(1,4),(1,6),(1,8),(1,9),(1,12),(3,4),(3,6),(3,8),(3,9),(3,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1674_q : Finset ℕ := ([0,1,3,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1674_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,13),(1,3),(1,4),(1,6),(1,8),(1,9),(1,13),(3,4),(3,6),(3,8),(3,9),(3,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1675_q : Finset ℕ := ([0,1,3,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1675_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,14),(1,3),(1,4),(1,6),(1,8),(1,9),(1,14),(3,4),(3,6),(3,8),(3,9),(3,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1676_q : Finset ℕ := ([0,1,3,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1676_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,12),(1,3),(1,4),(1,6),(1,8),(1,10),(1,12),(3,4),(3,6),(3,8),(3,10),(3,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1677_q : Finset ℕ := ([0,1,3,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1677_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,13),(1,3),(1,4),(1,6),(1,8),(1,10),(1,13),(3,4),(3,6),(3,8),(3,10),(3,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1678_q : Finset ℕ := ([0,1,3,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1678_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,14),(1,3),(1,4),(1,6),(1,8),(1,10),(1,14),(3,4),(3,6),(3,8),(3,10),(3,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1679_q : Finset ℕ := ([0,1,3,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1679_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,13),(1,3),(1,4),(1,6),(1,8),(1,11),(1,13),(3,4),(3,6),(3,8),(3,11),(3,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1680_q : Finset ℕ := ([0,1,3,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1680_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,14),(1,3),(1,4),(1,6),(1,8),(1,11),(1,14),(3,4),(3,6),(3,8),(3,11),(3,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1681_q : Finset ℕ := ([0,1,3,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1681_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(0,14),(1,3),(1,4),(1,6),(1,8),(1,12),(1,14),(3,4),(3,6),(3,8),(3,12),(3,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1682_q : Finset ℕ := ([0,1,3,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1682_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,13),(1,3),(1,4),(1,6),(1,9),(1,10),(1,13),(3,4),(3,6),(3,9),(3,10),(3,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1683_q : Finset ℕ := ([0,1,3,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1683_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,14),(1,3),(1,4),(1,6),(1,9),(1,10),(1,14),(3,4),(3,6),(3,9),(3,10),(3,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1684_q : Finset ℕ := ([0,1,3,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1684_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(0,14),(1,3),(1,4),(1,6),(1,9),(1,11),(1,14),(3,4),(3,6),(3,9),(3,11),(3,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1685_q : Finset ℕ := ([0,1,3,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1685_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(0,14),(1,3),(1,4),(1,6),(1,9),(1,12),(1,14),(3,4),(3,6),(3,9),(3,12),(3,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1686_q : Finset ℕ := ([0,1,3,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1686_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,10),(0,11),(0,14),(1,3),(1,4),(1,6),(1,10),(1,11),(1,14),(3,4),(3,6),(3,10),(3,11),(3,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1687_q : Finset ℕ := ([0,1,3,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1687_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(0,14),(1,3),(1,4),(1,7),(1,8),(1,11),(1,14),(3,4),(3,7),(3,8),(3,11),(3,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1688_q : Finset ℕ := ([0,1,3,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1688_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,9),(0,11),(0,14),(1,3),(1,4),(1,7),(1,9),(1,11),(1,14),(3,4),(3,7),(3,9),(3,11),(3,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1689_q : Finset ℕ := ([0,1,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1689_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(1,3),(1,5),(1,6),(1,8),(1,10),(1,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1690_q : Finset ℕ := ([0,1,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1690_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(1,3),(1,5),(1,6),(1,8),(1,10),(1,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1691_q : Finset ℕ := ([0,1,3,5,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1691_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,14),(1,3),(1,5),(1,6),(1,8),(1,10),(1,14),(3,5),(3,6),(3,8),(3,10),(3,14),(5,6),(5,8),(5,10),(5,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1692_q : Finset ℕ := ([0,1,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1692_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(1,3),(1,5),(1,6),(1,8),(1,11),(1,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1693_q : Finset ℕ := ([0,1,3,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1693_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,14),(1,3),(1,5),(1,6),(1,8),(1,11),(1,14),(3,5),(3,6),(3,8),(3,11),(3,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1694_q : Finset ℕ := ([0,1,3,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1694_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(0,14),(1,3),(1,5),(1,6),(1,8),(1,12),(1,14),(3,5),(3,6),(3,8),(3,12),(3,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1695_q : Finset ℕ := ([0,1,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1695_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(1,3),(1,5),(1,6),(1,9),(1,10),(1,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates054
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1696_q : Finset ℕ := ([0,1,3,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1696_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,14),(1,3),(1,5),(1,6),(1,9),(1,10),(1,14),(3,5),(3,6),(3,9),(3,10),(3,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1697_q : Finset ℕ := ([0,1,3,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1697_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,11),(0,14),(1,3),(1,5),(1,6),(1,9),(1,11),(1,14),(3,5),(3,6),(3,9),(3,11),(3,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1698_q : Finset ℕ := ([0,1,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1698_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(1,3),(1,5),(1,7),(1,8),(1,10),(1,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1699_q : Finset ℕ := ([0,1,3,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1699_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,14),(1,3),(1,5),(1,7),(1,8),(1,10),(1,14),(3,5),(3,7),(3,8),(3,10),(3,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1700_q : Finset ℕ := ([0,1,3,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1700_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(0,14),(1,3),(1,5),(1,7),(1,8),(1,11),(1,14),(3,5),(3,7),(3,8),(3,11),(3,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1701_q : Finset ℕ := ([0,1,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1701_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(1,3),(1,5),(1,7),(1,9),(1,10),(1,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1702_q : Finset ℕ := ([0,1,3,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1702_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,14),(1,3),(1,5),(1,7),(1,9),(1,10),(1,14),(3,5),(3,7),(3,9),(3,10),(3,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1703_q : Finset ℕ := ([0,1,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1703_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(1,3),(1,5),(1,7),(1,9),(1,11),(1,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1704_q : Finset ℕ := ([0,1,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1704_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(1,3),(1,5),(1,7),(1,9),(1,11),(1,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1705_q : Finset ℕ := ([0,1,3,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1705_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(0,14),(1,3),(1,5),(1,7),(1,9),(1,12),(1,14),(3,5),(3,7),(3,9),(3,12),(3,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1706_q : Finset ℕ := ([0,1,3,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1706_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,11),(0,14),(1,3),(1,5),(1,7),(1,10),(1,11),(1,14),(3,5),(3,7),(3,10),(3,11),(3,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1707_q : Finset ℕ := ([0,1,3,5,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1707_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(0,14),(1,3),(1,5),(1,7),(1,10),(1,12),(1,14),(3,5),(3,7),(3,10),(3,12),(3,14),(5,7),(5,10),(5,12),(5,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1708_q : Finset ℕ := ([0,1,3,5,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1708_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,9),(0,11),(0,14),(1,3),(1,5),(1,8),(1,9),(1,11),(1,14),(3,5),(3,8),(3,9),(3,11),(3,14),(5,8),(5,9),(5,11),(5,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1709_q : Finset ℕ := ([0,1,3,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1709_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,10),(0,11),(0,14),(1,3),(1,5),(1,8),(1,10),(1,11),(1,14),(3,5),(3,8),(3,10),(3,11),(3,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1710_q : Finset ℕ := ([0,1,3,6,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1710_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(0,14),(1,3),(1,6),(1,7),(1,9),(1,12),(1,14),(3,6),(3,7),(3,9),(3,12),(3,14),(6,7),(6,9),(6,12),(6,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1711_q : Finset ℕ := ([0,1,3,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1711_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,10),(0,11),(0,14),(1,3),(1,6),(1,7),(1,10),(1,11),(1,14),(3,6),(3,7),(3,10),(3,11),(3,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1712_q : Finset ℕ := ([0,2,3,5,6,8,9,11] : List ℕ).toFinset
noncomputable def certificate_1712_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,11),(2,3),(2,5),(2,6),(2,8),(2,9),(2,11),(3,5),(3,6),(3,8),(3,9),(3,11),(5,6),(5,8),(5,9),(5,11),(6,8),(6,9),(6,11),(8,9),(8,11),(9,11)]

noncomputable def certificate_1713_q : Finset ℕ := ([0,2,3,5,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1713_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,12),(2,3),(2,5),(2,6),(2,8),(2,9),(2,12),(3,5),(3,6),(3,8),(3,9),(3,12),(5,6),(5,8),(5,9),(5,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1714_q : Finset ℕ := ([0,2,3,5,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1714_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,13),(2,3),(2,5),(2,6),(2,8),(2,9),(2,13),(3,5),(3,6),(3,8),(3,9),(3,13),(5,6),(5,8),(5,9),(5,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1715_q : Finset ℕ := ([0,2,3,5,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1715_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,14),(2,3),(2,5),(2,6),(2,8),(2,9),(2,14),(3,5),(3,6),(3,8),(3,9),(3,14),(5,6),(5,8),(5,9),(5,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1716_q : Finset ℕ := ([0,2,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1716_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(2,3),(2,5),(2,6),(2,8),(2,10),(2,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1717_q : Finset ℕ := ([0,2,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1717_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(2,3),(2,5),(2,6),(2,8),(2,10),(2,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1718_q : Finset ℕ := ([0,2,3,5,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1718_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,14),(2,3),(2,5),(2,6),(2,8),(2,10),(2,14),(3,5),(3,6),(3,8),(3,10),(3,14),(5,6),(5,8),(5,10),(5,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1719_q : Finset ℕ := ([0,2,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1719_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(2,3),(2,5),(2,6),(2,8),(2,11),(2,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1720_q : Finset ℕ := ([0,2,3,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1720_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,14),(2,3),(2,5),(2,6),(2,8),(2,11),(2,14),(3,5),(3,6),(3,8),(3,11),(3,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1721_q : Finset ℕ := ([0,2,3,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1721_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(0,14),(2,3),(2,5),(2,6),(2,8),(2,12),(2,14),(3,5),(3,6),(3,8),(3,12),(3,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1722_q : Finset ℕ := ([0,2,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1722_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(2,3),(2,5),(2,6),(2,9),(2,10),(2,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1723_q : Finset ℕ := ([0,2,3,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1723_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,14),(2,3),(2,5),(2,6),(2,9),(2,10),(2,14),(3,5),(3,6),(3,9),(3,10),(3,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1724_q : Finset ℕ := ([0,2,3,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1724_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,11),(0,14),(2,3),(2,5),(2,6),(2,9),(2,11),(2,14),(3,5),(3,6),(3,9),(3,11),(3,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1725_q : Finset ℕ := ([0,2,3,5,7,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1725_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,12),(2,3),(2,5),(2,7),(2,8),(2,10),(2,12),(3,5),(3,7),(3,8),(3,10),(3,12),(5,7),(5,8),(5,10),(5,12),(7,8),(7,10),(7,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1726_q : Finset ℕ := ([0,2,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1726_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(2,3),(2,5),(2,7),(2,8),(2,10),(2,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1727_q : Finset ℕ := ([0,2,3,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1727_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,14),(2,3),(2,5),(2,7),(2,8),(2,10),(2,14),(3,5),(3,7),(3,8),(3,10),(3,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates055
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1728_q : Finset ℕ := ([0,2,3,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1728_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(0,14),(2,3),(2,5),(2,7),(2,8),(2,11),(2,14),(3,5),(3,7),(3,8),(3,11),(3,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1729_q : Finset ℕ := ([0,2,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1729_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(2,3),(2,5),(2,7),(2,9),(2,10),(2,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1730_q : Finset ℕ := ([0,2,3,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1730_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,14),(2,3),(2,5),(2,7),(2,9),(2,10),(2,14),(3,5),(3,7),(3,9),(3,10),(3,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1731_q : Finset ℕ := ([0,2,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1731_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(2,3),(2,5),(2,7),(2,9),(2,11),(2,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1732_q : Finset ℕ := ([0,2,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1732_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(2,3),(2,5),(2,7),(2,9),(2,11),(2,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1733_q : Finset ℕ := ([0,2,3,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1733_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(0,14),(2,3),(2,5),(2,7),(2,9),(2,12),(2,14),(3,5),(3,7),(3,9),(3,12),(3,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1734_q : Finset ℕ := ([0,2,3,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1734_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,11),(0,14),(2,3),(2,5),(2,7),(2,10),(2,11),(2,14),(3,5),(3,7),(3,10),(3,11),(3,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1735_q : Finset ℕ := ([0,2,3,5,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1735_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(0,14),(2,3),(2,5),(2,7),(2,10),(2,12),(2,14),(3,5),(3,7),(3,10),(3,12),(3,14),(5,7),(5,10),(5,12),(5,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1736_q : Finset ℕ := ([0,2,3,5,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1736_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,9),(0,11),(0,14),(2,3),(2,5),(2,8),(2,9),(2,11),(2,14),(3,5),(3,8),(3,9),(3,11),(3,14),(5,8),(5,9),(5,11),(5,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1737_q : Finset ℕ := ([0,2,3,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1737_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,10),(0,11),(0,14),(2,3),(2,5),(2,8),(2,10),(2,11),(2,14),(3,5),(3,8),(3,10),(3,11),(3,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1738_q : Finset ℕ := ([0,2,3,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1738_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,7),(0,10),(0,11),(0,14),(2,3),(2,6),(2,7),(2,10),(2,11),(2,14),(3,6),(3,7),(3,10),(3,11),(3,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1739_q : Finset ℕ := ([0,2,4,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1739_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,13),(2,4),(2,5),(2,7),(2,9),(2,10),(2,13),(4,5),(4,7),(4,9),(4,10),(4,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1740_q : Finset ℕ := ([0,2,4,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1740_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,14),(2,4),(2,5),(2,7),(2,9),(2,10),(2,14),(4,5),(4,7),(4,9),(4,10),(4,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1741_q : Finset ℕ := ([0,2,4,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1741_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,13),(2,4),(2,5),(2,7),(2,9),(2,11),(2,13),(4,5),(4,7),(4,9),(4,11),(4,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1742_q : Finset ℕ := ([0,2,4,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1742_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,14),(2,4),(2,5),(2,7),(2,9),(2,11),(2,14),(4,5),(4,7),(4,9),(4,11),(4,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1743_q : Finset ℕ := ([0,2,4,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1743_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(0,14),(2,4),(2,5),(2,7),(2,9),(2,12),(2,14),(4,5),(4,7),(4,9),(4,12),(4,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1744_q : Finset ℕ := ([0,2,4,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1744_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,10),(0,11),(0,14),(2,4),(2,5),(2,7),(2,10),(2,11),(2,14),(4,5),(4,7),(4,10),(4,11),(4,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1745_q : Finset ℕ := ([0,2,4,6,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1745_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,13),(2,4),(2,6),(2,7),(2,9),(2,11),(2,13),(4,6),(4,7),(4,9),(4,11),(4,13),(6,7),(6,9),(6,11),(6,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1746_q : Finset ℕ := ([0,2,4,6,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1746_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,14),(2,4),(2,6),(2,7),(2,9),(2,11),(2,14),(4,6),(4,7),(4,9),(4,11),(4,14),(6,7),(6,9),(6,11),(6,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1747_q : Finset ℕ := ([0,2,4,6,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1747_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(0,14),(2,4),(2,6),(2,7),(2,9),(2,12),(2,14),(4,6),(4,7),(4,9),(4,12),(4,14),(6,7),(6,9),(6,12),(6,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1748_q : Finset ℕ := ([0,2,4,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1748_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,10),(0,11),(0,14),(2,4),(2,6),(2,7),(2,10),(2,11),(2,14),(4,6),(4,7),(4,10),(4,11),(4,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1749_q : Finset ℕ := ([0,2,4,6,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1749_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,9),(0,11),(0,14),(2,4),(2,6),(2,8),(2,9),(2,11),(2,14),(4,6),(4,8),(4,9),(4,11),(4,14),(6,8),(6,9),(6,11),(6,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1750_q : Finset ℕ := ([0,2,4,6,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1750_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,11),(0,14),(2,4),(2,6),(2,8),(2,10),(2,11),(2,14),(4,6),(4,8),(4,10),(4,11),(4,14),(6,8),(6,10),(6,11),(6,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1751_q : Finset ℕ := ([0,2,4,6,8,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1751_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(0,14),(2,4),(2,6),(2,8),(2,10),(2,12),(2,14),(4,6),(4,8),(4,10),(4,12),(4,14),(6,8),(6,10),(6,12),(6,14),(8,10),(8,12),(8,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1752_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_1752_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_1753_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_1753_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_1754_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_1754_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_1755_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_1755_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_1756_q : Finset ℕ := ([0,1,2,3,4,5,6,11] : List ℕ).toFinset
noncomputable def certificate_1756_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,11),(1,2),(1,3),(1,4),(1,5),(1,6),(1,11),(2,3),(2,4),(2,5),(2,6),(2,11),(3,4),(3,5),(3,6),(3,11),(4,5),(4,6),(4,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_1757_q : Finset ℕ := ([0,1,2,3,4,5,6,12] : List ℕ).toFinset
noncomputable def certificate_1757_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,12),(1,2),(1,3),(1,4),(1,5),(1,6),(1,12),(2,3),(2,4),(2,5),(2,6),(2,12),(3,4),(3,5),(3,6),(3,12),(4,5),(4,6),(4,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_1758_q : Finset ℕ := ([0,1,2,3,4,5,6,13] : List ℕ).toFinset
noncomputable def certificate_1758_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,13),(1,2),(1,3),(1,4),(1,5),(1,6),(1,13),(2,3),(2,4),(2,5),(2,6),(2,13),(3,4),(3,5),(3,6),(3,13),(4,5),(4,6),(4,13),(5,6),(5,13),(6,13)]

noncomputable def certificate_1759_q : Finset ℕ := ([0,1,2,3,4,5,6,14] : List ℕ).toFinset
noncomputable def certificate_1759_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,14),(1,2),(1,3),(1,4),(1,5),(1,6),(1,14),(2,3),(2,4),(2,5),(2,6),(2,14),(3,4),(3,5),(3,6),(3,14),(4,5),(4,6),(4,14),(5,6),(5,14),(6,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates056
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1760_q : Finset ℕ := ([0,1,2,3,4,5,6,15] : List ℕ).toFinset
noncomputable def certificate_1760_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,15),(1,2),(1,3),(1,4),(1,5),(1,6),(1,15),(2,3),(2,4),(2,5),(2,6),(2,15),(3,4),(3,5),(3,6),(3,15),(4,5),(4,6),(4,15),(5,6),(5,15),(6,15)]

noncomputable def certificate_1761_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_1761_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_1762_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_1762_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_1763_q : Finset ℕ := ([0,1,2,3,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_1763_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,11),(1,2),(1,3),(1,4),(1,5),(1,7),(1,11),(2,3),(2,4),(2,5),(2,7),(2,11),(3,4),(3,5),(3,7),(3,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_1764_q : Finset ℕ := ([0,1,2,3,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_1764_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,12),(1,2),(1,3),(1,4),(1,5),(1,7),(1,12),(2,3),(2,4),(2,5),(2,7),(2,12),(3,4),(3,5),(3,7),(3,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_1765_q : Finset ℕ := ([0,1,2,3,4,5,7,13] : List ℕ).toFinset
noncomputable def certificate_1765_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,13),(1,2),(1,3),(1,4),(1,5),(1,7),(1,13),(2,3),(2,4),(2,5),(2,7),(2,13),(3,4),(3,5),(3,7),(3,13),(4,5),(4,7),(4,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_1766_q : Finset ℕ := ([0,1,2,3,4,5,7,14] : List ℕ).toFinset
noncomputable def certificate_1766_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,14),(1,2),(1,3),(1,4),(1,5),(1,7),(1,14),(2,3),(2,4),(2,5),(2,7),(2,14),(3,4),(3,5),(3,7),(3,14),(4,5),(4,7),(4,14),(5,7),(5,14),(7,14)]

noncomputable def certificate_1767_q : Finset ℕ := ([0,1,2,3,4,5,7,15] : List ℕ).toFinset
noncomputable def certificate_1767_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,15),(1,2),(1,3),(1,4),(1,5),(1,7),(1,15),(2,3),(2,4),(2,5),(2,7),(2,15),(3,4),(3,5),(3,7),(3,15),(4,5),(4,7),(4,15),(5,7),(5,15),(7,15)]

noncomputable def certificate_1768_q : Finset ℕ := ([0,1,2,3,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_1768_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,11),(1,2),(1,3),(1,4),(1,5),(1,8),(1,11),(2,3),(2,4),(2,5),(2,8),(2,11),(3,4),(3,5),(3,8),(3,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_1769_q : Finset ℕ := ([0,1,2,3,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_1769_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,12),(1,2),(1,3),(1,4),(1,5),(1,8),(1,12),(2,3),(2,4),(2,5),(2,8),(2,12),(3,4),(3,5),(3,8),(3,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

noncomputable def certificate_1770_q : Finset ℕ := ([0,1,2,3,4,5,8,13] : List ℕ).toFinset
noncomputable def certificate_1770_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,13),(1,2),(1,3),(1,4),(1,5),(1,8),(1,13),(2,3),(2,4),(2,5),(2,8),(2,13),(3,4),(3,5),(3,8),(3,13),(4,5),(4,8),(4,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_1771_q : Finset ℕ := ([0,1,2,3,4,5,8,14] : List ℕ).toFinset
noncomputable def certificate_1771_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,14),(1,2),(1,3),(1,4),(1,5),(1,8),(1,14),(2,3),(2,4),(2,5),(2,8),(2,14),(3,4),(3,5),(3,8),(3,14),(4,5),(4,8),(4,14),(5,8),(5,14),(8,14)]

noncomputable def certificate_1772_q : Finset ℕ := ([0,1,2,3,4,5,8,15] : List ℕ).toFinset
noncomputable def certificate_1772_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,15),(1,2),(1,3),(1,4),(1,5),(1,8),(1,15),(2,3),(2,4),(2,5),(2,8),(2,15),(3,4),(3,5),(3,8),(3,15),(4,5),(4,8),(4,15),(5,8),(5,15),(8,15)]

noncomputable def certificate_1773_q : Finset ℕ := ([0,1,2,3,4,5,9,13] : List ℕ).toFinset
noncomputable def certificate_1773_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,13),(1,2),(1,3),(1,4),(1,5),(1,9),(1,13),(2,3),(2,4),(2,5),(2,9),(2,13),(3,4),(3,5),(3,9),(3,13),(4,5),(4,9),(4,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_1774_q : Finset ℕ := ([0,1,2,3,4,5,9,14] : List ℕ).toFinset
noncomputable def certificate_1774_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,14),(1,2),(1,3),(1,4),(1,5),(1,9),(1,14),(2,3),(2,4),(2,5),(2,9),(2,14),(3,4),(3,5),(3,9),(3,14),(4,5),(4,9),(4,14),(5,9),(5,14),(9,14)]

noncomputable def certificate_1775_q : Finset ℕ := ([0,1,2,3,4,5,9,15] : List ℕ).toFinset
noncomputable def certificate_1775_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,15),(1,2),(1,3),(1,4),(1,5),(1,9),(1,15),(2,3),(2,4),(2,5),(2,9),(2,15),(3,4),(3,5),(3,9),(3,15),(4,5),(4,9),(4,15),(5,9),(5,15),(9,15)]

noncomputable def certificate_1776_q : Finset ℕ := ([0,1,2,3,4,5,10,15] : List ℕ).toFinset
noncomputable def certificate_1776_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(0,15),(1,2),(1,3),(1,4),(1,5),(1,10),(1,15),(2,3),(2,4),(2,5),(2,10),(2,15),(3,4),(3,5),(3,10),(3,15),(4,5),(4,10),(4,15),(5,10),(5,15),(10,15)]

noncomputable def certificate_1777_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_1777_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_1778_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_1778_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_1779_q : Finset ℕ := ([0,1,2,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_1779_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,11),(1,2),(1,3),(1,4),(1,6),(1,7),(1,11),(2,3),(2,4),(2,6),(2,7),(2,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_1780_q : Finset ℕ := ([0,1,2,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_1780_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,12),(1,2),(1,3),(1,4),(1,6),(1,7),(1,12),(2,3),(2,4),(2,6),(2,7),(2,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_1781_q : Finset ℕ := ([0,1,2,3,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_1781_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,13),(1,2),(1,3),(1,4),(1,6),(1,7),(1,13),(2,3),(2,4),(2,6),(2,7),(2,13),(3,4),(3,6),(3,7),(3,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_1782_q : Finset ℕ := ([0,1,2,3,4,6,7,14] : List ℕ).toFinset
noncomputable def certificate_1782_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,14),(1,2),(1,3),(1,4),(1,6),(1,7),(1,14),(2,3),(2,4),(2,6),(2,7),(2,14),(3,4),(3,6),(3,7),(3,14),(4,6),(4,7),(4,14),(6,7),(6,14),(7,14)]

noncomputable def certificate_1783_q : Finset ℕ := ([0,1,2,3,4,6,7,15] : List ℕ).toFinset
noncomputable def certificate_1783_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,15),(1,2),(1,3),(1,4),(1,6),(1,7),(1,15),(2,3),(2,4),(2,6),(2,7),(2,15),(3,4),(3,6),(3,7),(3,15),(4,6),(4,7),(4,15),(6,7),(6,15),(7,15)]

noncomputable def certificate_1784_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1784_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1785_q : Finset ℕ := ([0,1,2,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1785_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,11),(1,2),(1,3),(1,4),(1,6),(1,8),(1,11),(2,3),(2,4),(2,6),(2,8),(2,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1786_q : Finset ℕ := ([0,1,2,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1786_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,12),(1,2),(1,3),(1,4),(1,6),(1,8),(1,12),(2,3),(2,4),(2,6),(2,8),(2,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1787_q : Finset ℕ := ([0,1,2,3,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1787_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,13),(1,2),(1,3),(1,4),(1,6),(1,8),(1,13),(2,3),(2,4),(2,6),(2,8),(2,13),(3,4),(3,6),(3,8),(3,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1788_q : Finset ℕ := ([0,1,2,3,4,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1788_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,14),(1,2),(1,3),(1,4),(1,6),(1,8),(1,14),(2,3),(2,4),(2,6),(2,8),(2,14),(3,4),(3,6),(3,8),(3,14),(4,6),(4,8),(4,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1789_q : Finset ℕ := ([0,1,2,3,4,6,8,15] : List ℕ).toFinset
noncomputable def certificate_1789_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,15),(1,2),(1,3),(1,4),(1,6),(1,8),(1,15),(2,3),(2,4),(2,6),(2,8),(2,15),(3,4),(3,6),(3,8),(3,15),(4,6),(4,8),(4,15),(6,8),(6,15),(8,15)]

noncomputable def certificate_1790_q : Finset ℕ := ([0,1,2,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_1790_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,11),(1,2),(1,3),(1,4),(1,6),(1,9),(1,11),(2,3),(2,4),(2,6),(2,9),(2,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_1791_q : Finset ℕ := ([0,1,2,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1791_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,12),(1,2),(1,3),(1,4),(1,6),(1,9),(1,12),(2,3),(2,4),(2,6),(2,9),(2,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates057
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1792_q : Finset ℕ := ([0,1,2,3,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1792_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,13),(1,2),(1,3),(1,4),(1,6),(1,9),(1,13),(2,3),(2,4),(2,6),(2,9),(2,13),(3,4),(3,6),(3,9),(3,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1793_q : Finset ℕ := ([0,1,2,3,4,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1793_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,14),(1,2),(1,3),(1,4),(1,6),(1,9),(1,14),(2,3),(2,4),(2,6),(2,9),(2,14),(3,4),(3,6),(3,9),(3,14),(4,6),(4,9),(4,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1794_q : Finset ℕ := ([0,1,2,3,4,6,9,15] : List ℕ).toFinset
noncomputable def certificate_1794_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,15),(1,2),(1,3),(1,4),(1,6),(1,9),(1,15),(2,3),(2,4),(2,6),(2,9),(2,15),(3,4),(3,6),(3,9),(3,15),(4,6),(4,9),(4,15),(6,9),(6,15),(9,15)]

noncomputable def certificate_1795_q : Finset ℕ := ([0,1,2,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_1795_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,12),(1,2),(1,3),(1,4),(1,6),(1,10),(1,12),(2,3),(2,4),(2,6),(2,10),(2,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

noncomputable def certificate_1796_q : Finset ℕ := ([0,1,2,3,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_1796_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,13),(1,2),(1,3),(1,4),(1,6),(1,10),(1,13),(2,3),(2,4),(2,6),(2,10),(2,13),(3,4),(3,6),(3,10),(3,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_1797_q : Finset ℕ := ([0,1,2,3,4,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1797_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,14),(1,2),(1,3),(1,4),(1,6),(1,10),(1,14),(2,3),(2,4),(2,6),(2,10),(2,14),(3,4),(3,6),(3,10),(3,14),(4,6),(4,10),(4,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1798_q : Finset ℕ := ([0,1,2,3,4,6,10,15] : List ℕ).toFinset
noncomputable def certificate_1798_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,15),(1,2),(1,3),(1,4),(1,6),(1,10),(1,15),(2,3),(2,4),(2,6),(2,10),(2,15),(3,4),(3,6),(3,10),(3,15),(4,6),(4,10),(4,15),(6,10),(6,15),(10,15)]

noncomputable def certificate_1799_q : Finset ℕ := ([0,1,2,3,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_1799_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,13),(1,2),(1,3),(1,4),(1,6),(1,11),(1,13),(2,3),(2,4),(2,6),(2,11),(2,13),(3,4),(3,6),(3,11),(3,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_1800_q : Finset ℕ := ([0,1,2,3,4,6,11,14] : List ℕ).toFinset
noncomputable def certificate_1800_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,14),(1,2),(1,3),(1,4),(1,6),(1,11),(1,14),(2,3),(2,4),(2,6),(2,11),(2,14),(3,4),(3,6),(3,11),(3,14),(4,6),(4,11),(4,14),(6,11),(6,14),(11,14)]

noncomputable def certificate_1801_q : Finset ℕ := ([0,1,2,3,4,6,11,15] : List ℕ).toFinset
noncomputable def certificate_1801_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,15),(1,2),(1,3),(1,4),(1,6),(1,11),(1,15),(2,3),(2,4),(2,6),(2,11),(2,15),(3,4),(3,6),(3,11),(3,15),(4,6),(4,11),(4,15),(6,11),(6,15),(11,15)]

noncomputable def certificate_1802_q : Finset ℕ := ([0,1,2,3,4,6,12,14] : List ℕ).toFinset
noncomputable def certificate_1802_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(0,14),(1,2),(1,3),(1,4),(1,6),(1,12),(1,14),(2,3),(2,4),(2,6),(2,12),(2,14),(3,4),(3,6),(3,12),(3,14),(4,6),(4,12),(4,14),(6,12),(6,14),(12,14)]

noncomputable def certificate_1803_q : Finset ℕ := ([0,1,2,3,4,6,12,15] : List ℕ).toFinset
noncomputable def certificate_1803_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(0,15),(1,2),(1,3),(1,4),(1,6),(1,12),(1,15),(2,3),(2,4),(2,6),(2,12),(2,15),(3,4),(3,6),(3,12),(3,15),(4,6),(4,12),(4,15),(6,12),(6,15),(12,15)]

noncomputable def certificate_1804_q : Finset ℕ := ([0,1,2,3,4,6,13,15] : List ℕ).toFinset
noncomputable def certificate_1804_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,13),(0,15),(1,2),(1,3),(1,4),(1,6),(1,13),(1,15),(2,3),(2,4),(2,6),(2,13),(2,15),(3,4),(3,6),(3,13),(3,15),(4,6),(4,13),(4,15),(6,13),(6,15),(13,15)]

noncomputable def certificate_1805_q : Finset ℕ := ([0,1,2,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1805_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,11),(1,2),(1,3),(1,4),(1,7),(1,8),(1,11),(2,3),(2,4),(2,7),(2,8),(2,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1806_q : Finset ℕ := ([0,1,2,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1806_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,12),(1,2),(1,3),(1,4),(1,7),(1,8),(1,12),(2,3),(2,4),(2,7),(2,8),(2,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1807_q : Finset ℕ := ([0,1,2,3,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1807_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,13),(1,2),(1,3),(1,4),(1,7),(1,8),(1,13),(2,3),(2,4),(2,7),(2,8),(2,13),(3,4),(3,7),(3,8),(3,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1808_q : Finset ℕ := ([0,1,2,3,4,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1808_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,14),(1,2),(1,3),(1,4),(1,7),(1,8),(1,14),(2,3),(2,4),(2,7),(2,8),(2,14),(3,4),(3,7),(3,8),(3,14),(4,7),(4,8),(4,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1809_q : Finset ℕ := ([0,1,2,3,4,7,8,15] : List ℕ).toFinset
noncomputable def certificate_1809_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,15),(1,2),(1,3),(1,4),(1,7),(1,8),(1,15),(2,3),(2,4),(2,7),(2,8),(2,15),(3,4),(3,7),(3,8),(3,15),(4,7),(4,8),(4,15),(7,8),(7,15),(8,15)]

noncomputable def certificate_1810_q : Finset ℕ := ([0,1,2,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1810_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,12),(1,2),(1,3),(1,4),(1,7),(1,9),(1,12),(2,3),(2,4),(2,7),(2,9),(2,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1811_q : Finset ℕ := ([0,1,2,3,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1811_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,13),(1,2),(1,3),(1,4),(1,7),(1,9),(1,13),(2,3),(2,4),(2,7),(2,9),(2,13),(3,4),(3,7),(3,9),(3,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1812_q : Finset ℕ := ([0,1,2,3,4,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1812_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,14),(1,2),(1,3),(1,4),(1,7),(1,9),(1,14),(2,3),(2,4),(2,7),(2,9),(2,14),(3,4),(3,7),(3,9),(3,14),(4,7),(4,9),(4,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1813_q : Finset ℕ := ([0,1,2,3,4,7,9,15] : List ℕ).toFinset
noncomputable def certificate_1813_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,15),(1,2),(1,3),(1,4),(1,7),(1,9),(1,15),(2,3),(2,4),(2,7),(2,9),(2,15),(3,4),(3,7),(3,9),(3,15),(4,7),(4,9),(4,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_1814_q : Finset ℕ := ([0,1,2,3,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1814_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,13),(1,2),(1,3),(1,4),(1,7),(1,10),(1,13),(2,3),(2,4),(2,7),(2,10),(2,13),(3,4),(3,7),(3,10),(3,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1815_q : Finset ℕ := ([0,1,2,3,4,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1815_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,14),(1,2),(1,3),(1,4),(1,7),(1,10),(1,14),(2,3),(2,4),(2,7),(2,10),(2,14),(3,4),(3,7),(3,10),(3,14),(4,7),(4,10),(4,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1816_q : Finset ℕ := ([0,1,2,3,4,7,10,15] : List ℕ).toFinset
noncomputable def certificate_1816_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,15),(1,2),(1,3),(1,4),(1,7),(1,10),(1,15),(2,3),(2,4),(2,7),(2,10),(2,15),(3,4),(3,7),(3,10),(3,15),(4,7),(4,10),(4,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_1817_q : Finset ℕ := ([0,1,2,3,4,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1817_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(0,14),(1,2),(1,3),(1,4),(1,7),(1,11),(1,14),(2,3),(2,4),(2,7),(2,11),(2,14),(3,4),(3,7),(3,11),(3,14),(4,7),(4,11),(4,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1818_q : Finset ℕ := ([0,1,2,3,4,7,11,15] : List ℕ).toFinset
noncomputable def certificate_1818_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(0,15),(1,2),(1,3),(1,4),(1,7),(1,11),(1,15),(2,3),(2,4),(2,7),(2,11),(2,15),(3,4),(3,7),(3,11),(3,15),(4,7),(4,11),(4,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_1819_q : Finset ℕ := ([0,1,2,3,4,7,12,15] : List ℕ).toFinset
noncomputable def certificate_1819_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,12),(0,15),(1,2),(1,3),(1,4),(1,7),(1,12),(1,15),(2,3),(2,4),(2,7),(2,12),(2,15),(3,4),(3,7),(3,12),(3,15),(4,7),(4,12),(4,15),(7,12),(7,15),(12,15)]

noncomputable def certificate_1820_q : Finset ℕ := ([0,1,2,3,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1820_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,13),(1,2),(1,3),(1,4),(1,8),(1,9),(1,13),(2,3),(2,4),(2,8),(2,9),(2,13),(3,4),(3,8),(3,9),(3,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1821_q : Finset ℕ := ([0,1,2,3,4,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1821_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,14),(1,2),(1,3),(1,4),(1,8),(1,9),(1,14),(2,3),(2,4),(2,8),(2,9),(2,14),(3,4),(3,8),(3,9),(3,14),(4,8),(4,9),(4,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1822_q : Finset ℕ := ([0,1,2,3,4,8,9,15] : List ℕ).toFinset
noncomputable def certificate_1822_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,15),(1,2),(1,3),(1,4),(1,8),(1,9),(1,15),(2,3),(2,4),(2,8),(2,9),(2,15),(3,4),(3,8),(3,9),(3,15),(4,8),(4,9),(4,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_1823_q : Finset ℕ := ([0,1,2,3,4,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1823_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,10),(0,14),(1,2),(1,3),(1,4),(1,8),(1,10),(1,14),(2,3),(2,4),(2,8),(2,10),(2,14),(3,4),(3,8),(3,10),(3,14),(4,8),(4,10),(4,14),(8,10),(8,14),(10,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates058
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1824_q : Finset ℕ := ([0,1,2,3,4,8,10,15] : List ℕ).toFinset
noncomputable def certificate_1824_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,8),(0,10),(0,15),(1,2),(1,3),(1,4),(1,8),(1,10),(1,15),(2,3),(2,4),(2,8),(2,10),(2,15),(3,4),(3,8),(3,10),(3,15),(4,8),(4,10),(4,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_1825_q : Finset ℕ := ([0,1,2,3,4,8,11,15] : List ℕ).toFinset
noncomputable def certificate_1825_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,8),(0,11),(0,15),(1,2),(1,3),(1,4),(1,8),(1,11),(1,15),(2,3),(2,4),(2,8),(2,11),(2,15),(3,4),(3,8),(3,11),(3,15),(4,8),(4,11),(4,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_1826_q : Finset ℕ := ([0,1,2,3,4,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1826_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,9),(0,10),(0,15),(1,2),(1,3),(1,4),(1,9),(1,10),(1,15),(2,3),(2,4),(2,9),(2,10),(2,15),(3,4),(3,9),(3,10),(3,15),(4,9),(4,10),(4,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_1827_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_1827_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_1828_q : Finset ℕ := ([0,1,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_1828_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(1,2),(1,3),(1,5),(1,6),(1,8),(1,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_1829_q : Finset ℕ := ([0,1,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_1829_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(1,2),(1,3),(1,5),(1,6),(1,8),(1,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_1830_q : Finset ℕ := ([0,1,2,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_1830_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(1,2),(1,3),(1,5),(1,6),(1,8),(1,13),(2,3),(2,5),(2,6),(2,8),(2,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_1831_q : Finset ℕ := ([0,1,2,3,5,6,8,14] : List ℕ).toFinset
noncomputable def certificate_1831_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,14),(1,2),(1,3),(1,5),(1,6),(1,8),(1,14),(2,3),(2,5),(2,6),(2,8),(2,14),(3,5),(3,6),(3,8),(3,14),(5,6),(5,8),(5,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_1832_q : Finset ℕ := ([0,1,2,3,5,6,8,15] : List ℕ).toFinset
noncomputable def certificate_1832_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,15),(1,2),(1,3),(1,5),(1,6),(1,8),(1,15),(2,3),(2,5),(2,6),(2,8),(2,15),(3,5),(3,6),(3,8),(3,15),(5,6),(5,8),(5,15),(6,8),(6,15),(8,15)]

noncomputable def certificate_1833_q : Finset ℕ := ([0,1,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_1833_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(1,2),(1,3),(1,5),(1,6),(1,9),(1,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_1834_q : Finset ℕ := ([0,1,2,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_1834_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(1,2),(1,3),(1,5),(1,6),(1,9),(1,13),(2,3),(2,5),(2,6),(2,9),(2,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_1835_q : Finset ℕ := ([0,1,2,3,5,6,9,14] : List ℕ).toFinset
noncomputable def certificate_1835_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,14),(1,2),(1,3),(1,5),(1,6),(1,9),(1,14),(2,3),(2,5),(2,6),(2,9),(2,14),(3,5),(3,6),(3,9),(3,14),(5,6),(5,9),(5,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_1836_q : Finset ℕ := ([0,1,2,3,5,6,9,15] : List ℕ).toFinset
noncomputable def certificate_1836_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,15),(1,2),(1,3),(1,5),(1,6),(1,9),(1,15),(2,3),(2,5),(2,6),(2,9),(2,15),(3,5),(3,6),(3,9),(3,15),(5,6),(5,9),(5,15),(6,9),(6,15),(9,15)]

noncomputable def certificate_1837_q : Finset ℕ := ([0,1,2,3,5,6,10,14] : List ℕ).toFinset
noncomputable def certificate_1837_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(0,14),(1,2),(1,3),(1,5),(1,6),(1,10),(1,14),(2,3),(2,5),(2,6),(2,10),(2,14),(3,5),(3,6),(3,10),(3,14),(5,6),(5,10),(5,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_1838_q : Finset ℕ := ([0,1,2,3,5,6,10,15] : List ℕ).toFinset
noncomputable def certificate_1838_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(0,15),(1,2),(1,3),(1,5),(1,6),(1,10),(1,15),(2,3),(2,5),(2,6),(2,10),(2,15),(3,5),(3,6),(3,10),(3,15),(5,6),(5,10),(5,15),(6,10),(6,15),(10,15)]

noncomputable def certificate_1839_q : Finset ℕ := ([0,1,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1839_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(1,2),(1,3),(1,5),(1,7),(1,8),(1,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1840_q : Finset ℕ := ([0,1,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1840_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(1,2),(1,3),(1,5),(1,7),(1,8),(1,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1841_q : Finset ℕ := ([0,1,2,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1841_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,13),(1,2),(1,3),(1,5),(1,7),(1,8),(1,13),(2,3),(2,5),(2,7),(2,8),(2,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1842_q : Finset ℕ := ([0,1,2,3,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1842_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,14),(1,2),(1,3),(1,5),(1,7),(1,8),(1,14),(2,3),(2,5),(2,7),(2,8),(2,14),(3,5),(3,7),(3,8),(3,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1843_q : Finset ℕ := ([0,1,2,3,5,7,8,15] : List ℕ).toFinset
noncomputable def certificate_1843_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,15),(1,2),(1,3),(1,5),(1,7),(1,8),(1,15),(2,3),(2,5),(2,7),(2,8),(2,15),(3,5),(3,7),(3,8),(3,15),(5,7),(5,8),(5,15),(7,8),(7,15),(8,15)]

noncomputable def certificate_1844_q : Finset ℕ := ([0,1,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1844_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(1,2),(1,3),(1,5),(1,7),(1,9),(1,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1845_q : Finset ℕ := ([0,1,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1845_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(1,2),(1,3),(1,5),(1,7),(1,9),(1,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1846_q : Finset ℕ := ([0,1,2,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1846_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(1,2),(1,3),(1,5),(1,7),(1,9),(1,13),(2,3),(2,5),(2,7),(2,9),(2,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1847_q : Finset ℕ := ([0,1,2,3,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1847_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,14),(1,2),(1,3),(1,5),(1,7),(1,9),(1,14),(2,3),(2,5),(2,7),(2,9),(2,14),(3,5),(3,7),(3,9),(3,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1848_q : Finset ℕ := ([0,1,2,3,5,7,9,15] : List ℕ).toFinset
noncomputable def certificate_1848_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,15),(1,2),(1,3),(1,5),(1,7),(1,9),(1,15),(2,3),(2,5),(2,7),(2,9),(2,15),(3,5),(3,7),(3,9),(3,15),(5,7),(5,9),(5,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_1849_q : Finset ℕ := ([0,1,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1849_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(1,2),(1,3),(1,5),(1,7),(1,10),(1,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1850_q : Finset ℕ := ([0,1,2,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1850_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(1,2),(1,3),(1,5),(1,7),(1,10),(1,13),(2,3),(2,5),(2,7),(2,10),(2,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1851_q : Finset ℕ := ([0,1,2,3,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1851_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,14),(1,2),(1,3),(1,5),(1,7),(1,10),(1,14),(2,3),(2,5),(2,7),(2,10),(2,14),(3,5),(3,7),(3,10),(3,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1852_q : Finset ℕ := ([0,1,2,3,5,7,10,15] : List ℕ).toFinset
noncomputable def certificate_1852_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,15),(1,2),(1,3),(1,5),(1,7),(1,10),(1,15),(2,3),(2,5),(2,7),(2,10),(2,15),(3,5),(3,7),(3,10),(3,15),(5,7),(5,10),(5,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_1853_q : Finset ℕ := ([0,1,2,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1853_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(1,2),(1,3),(1,5),(1,7),(1,11),(1,13),(2,3),(2,5),(2,7),(2,11),(2,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1854_q : Finset ℕ := ([0,1,2,3,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1854_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,14),(1,2),(1,3),(1,5),(1,7),(1,11),(1,14),(2,3),(2,5),(2,7),(2,11),(2,14),(3,5),(3,7),(3,11),(3,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1855_q : Finset ℕ := ([0,1,2,3,5,7,11,15] : List ℕ).toFinset
noncomputable def certificate_1855_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,15),(1,2),(1,3),(1,5),(1,7),(1,11),(1,15),(2,3),(2,5),(2,7),(2,11),(2,15),(3,5),(3,7),(3,11),(3,15),(5,7),(5,11),(5,15),(7,11),(7,15),(11,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates059
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1856_q : Finset ℕ := ([0,1,2,3,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1856_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(0,14),(1,2),(1,3),(1,5),(1,7),(1,12),(1,14),(2,3),(2,5),(2,7),(2,12),(2,14),(3,5),(3,7),(3,12),(3,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1857_q : Finset ℕ := ([0,1,2,3,5,7,12,15] : List ℕ).toFinset
noncomputable def certificate_1857_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(0,15),(1,2),(1,3),(1,5),(1,7),(1,12),(1,15),(2,3),(2,5),(2,7),(2,12),(2,15),(3,5),(3,7),(3,12),(3,15),(5,7),(5,12),(5,15),(7,12),(7,15),(12,15)]

noncomputable def certificate_1858_q : Finset ℕ := ([0,1,2,3,5,7,13,15] : List ℕ).toFinset
noncomputable def certificate_1858_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,13),(0,15),(1,2),(1,3),(1,5),(1,7),(1,13),(1,15),(2,3),(2,5),(2,7),(2,13),(2,15),(3,5),(3,7),(3,13),(3,15),(5,7),(5,13),(5,15),(7,13),(7,15),(13,15)]

noncomputable def certificate_1859_q : Finset ℕ := ([0,1,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1859_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(1,2),(1,3),(1,5),(1,8),(1,9),(1,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1860_q : Finset ℕ := ([0,1,2,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1860_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,13),(1,2),(1,3),(1,5),(1,8),(1,9),(1,13),(2,3),(2,5),(2,8),(2,9),(2,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1861_q : Finset ℕ := ([0,1,2,3,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1861_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,14),(1,2),(1,3),(1,5),(1,8),(1,9),(1,14),(2,3),(2,5),(2,8),(2,9),(2,14),(3,5),(3,8),(3,9),(3,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1862_q : Finset ℕ := ([0,1,2,3,5,8,9,15] : List ℕ).toFinset
noncomputable def certificate_1862_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,15),(1,2),(1,3),(1,5),(1,8),(1,9),(1,15),(2,3),(2,5),(2,8),(2,9),(2,15),(3,5),(3,8),(3,9),(3,15),(5,8),(5,9),(5,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_1863_q : Finset ℕ := ([0,1,2,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1863_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(1,2),(1,3),(1,5),(1,8),(1,10),(1,13),(2,3),(2,5),(2,8),(2,10),(2,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1864_q : Finset ℕ := ([0,1,2,3,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1864_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,14),(1,2),(1,3),(1,5),(1,8),(1,10),(1,14),(2,3),(2,5),(2,8),(2,10),(2,14),(3,5),(3,8),(3,10),(3,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1865_q : Finset ℕ := ([0,1,2,3,5,8,10,15] : List ℕ).toFinset
noncomputable def certificate_1865_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,15),(1,2),(1,3),(1,5),(1,8),(1,10),(1,15),(2,3),(2,5),(2,8),(2,10),(2,15),(3,5),(3,8),(3,10),(3,15),(5,8),(5,10),(5,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_1866_q : Finset ℕ := ([0,1,2,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1866_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(1,2),(1,3),(1,5),(1,8),(1,11),(1,13),(2,3),(2,5),(2,8),(2,11),(2,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1867_q : Finset ℕ := ([0,1,2,3,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1867_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,14),(1,2),(1,3),(1,5),(1,8),(1,11),(1,14),(2,3),(2,5),(2,8),(2,11),(2,14),(3,5),(3,8),(3,11),(3,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1868_q : Finset ℕ := ([0,1,2,3,5,8,11,15] : List ℕ).toFinset
noncomputable def certificate_1868_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,15),(1,2),(1,3),(1,5),(1,8),(1,11),(1,15),(2,3),(2,5),(2,8),(2,11),(2,15),(3,5),(3,8),(3,11),(3,15),(5,8),(5,11),(5,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_1869_q : Finset ℕ := ([0,1,2,3,5,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1869_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(0,14),(1,2),(1,3),(1,5),(1,8),(1,12),(1,14),(2,3),(2,5),(2,8),(2,12),(2,14),(3,5),(3,8),(3,12),(3,14),(5,8),(5,12),(5,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1870_q : Finset ℕ := ([0,1,2,3,5,8,12,15] : List ℕ).toFinset
noncomputable def certificate_1870_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(0,15),(1,2),(1,3),(1,5),(1,8),(1,12),(1,15),(2,3),(2,5),(2,8),(2,12),(2,15),(3,5),(3,8),(3,12),(3,15),(5,8),(5,12),(5,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_1871_q : Finset ℕ := ([0,1,2,3,5,8,13,15] : List ℕ).toFinset
noncomputable def certificate_1871_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,13),(0,15),(1,2),(1,3),(1,5),(1,8),(1,13),(1,15),(2,3),(2,5),(2,8),(2,13),(2,15),(3,5),(3,8),(3,13),(3,15),(5,8),(5,13),(5,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_1872_q : Finset ℕ := ([0,1,2,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1872_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(1,2),(1,3),(1,5),(1,9),(1,10),(1,13),(2,3),(2,5),(2,9),(2,10),(2,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1873_q : Finset ℕ := ([0,1,2,3,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1873_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,14),(1,2),(1,3),(1,5),(1,9),(1,10),(1,14),(2,3),(2,5),(2,9),(2,10),(2,14),(3,5),(3,9),(3,10),(3,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1874_q : Finset ℕ := ([0,1,2,3,5,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1874_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,15),(1,2),(1,3),(1,5),(1,9),(1,10),(1,15),(2,3),(2,5),(2,9),(2,10),(2,15),(3,5),(3,9),(3,10),(3,15),(5,9),(5,10),(5,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_1875_q : Finset ℕ := ([0,1,2,3,5,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1875_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(0,14),(1,2),(1,3),(1,5),(1,9),(1,11),(1,14),(2,3),(2,5),(2,9),(2,11),(2,14),(3,5),(3,9),(3,11),(3,14),(5,9),(5,11),(5,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1876_q : Finset ℕ := ([0,1,2,3,5,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1876_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(0,15),(1,2),(1,3),(1,5),(1,9),(1,11),(1,15),(2,3),(2,5),(2,9),(2,11),(2,15),(3,5),(3,9),(3,11),(3,15),(5,9),(5,11),(5,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1877_q : Finset ℕ := ([0,1,2,3,5,9,12,15] : List ℕ).toFinset
noncomputable def certificate_1877_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,12),(0,15),(1,2),(1,3),(1,5),(1,9),(1,12),(1,15),(2,3),(2,5),(2,9),(2,12),(2,15),(3,5),(3,9),(3,12),(3,15),(5,9),(5,12),(5,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_1878_q : Finset ℕ := ([0,1,2,3,5,9,13,15] : List ℕ).toFinset
noncomputable def certificate_1878_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,13),(0,15),(1,2),(1,3),(1,5),(1,9),(1,13),(1,15),(2,3),(2,5),(2,9),(2,13),(2,15),(3,5),(3,9),(3,13),(3,15),(5,9),(5,13),(5,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_1879_q : Finset ℕ := ([0,1,2,3,5,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1879_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,10),(0,11),(0,14),(1,2),(1,3),(1,5),(1,10),(1,11),(1,14),(2,3),(2,5),(2,10),(2,11),(2,14),(3,5),(3,10),(3,11),(3,14),(5,10),(5,11),(5,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1880_q : Finset ℕ := ([0,1,2,3,5,10,11,15] : List ℕ).toFinset
noncomputable def certificate_1880_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,10),(0,11),(0,15),(1,2),(1,3),(1,5),(1,10),(1,11),(1,15),(2,3),(2,5),(2,10),(2,11),(2,15),(3,5),(3,10),(3,11),(3,15),(5,10),(5,11),(5,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_1881_q : Finset ℕ := ([0,1,2,3,5,10,12,15] : List ℕ).toFinset
noncomputable def certificate_1881_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,10),(0,12),(0,15),(1,2),(1,3),(1,5),(1,10),(1,12),(1,15),(2,3),(2,5),(2,10),(2,12),(2,15),(3,5),(3,10),(3,12),(3,15),(5,10),(5,12),(5,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_1882_q : Finset ℕ := ([0,1,2,3,5,11,12,15] : List ℕ).toFinset
noncomputable def certificate_1882_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,11),(0,12),(0,15),(1,2),(1,3),(1,5),(1,11),(1,12),(1,15),(2,3),(2,5),(2,11),(2,12),(2,15),(3,5),(3,11),(3,12),(3,15),(5,11),(5,12),(5,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_1883_q : Finset ℕ := ([0,1,2,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1883_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(1,2),(1,3),(1,6),(1,7),(1,10),(1,13),(2,3),(2,6),(2,7),(2,10),(2,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1884_q : Finset ℕ := ([0,1,2,3,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1884_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,14),(1,2),(1,3),(1,6),(1,7),(1,10),(1,14),(2,3),(2,6),(2,7),(2,10),(2,14),(3,6),(3,7),(3,10),(3,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1885_q : Finset ℕ := ([0,1,2,3,6,7,10,15] : List ℕ).toFinset
noncomputable def certificate_1885_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,15),(1,2),(1,3),(1,6),(1,7),(1,10),(1,15),(2,3),(2,6),(2,7),(2,10),(2,15),(3,6),(3,7),(3,10),(3,15),(6,7),(6,10),(6,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_1886_q : Finset ℕ := ([0,1,2,3,6,7,11,15] : List ℕ).toFinset
noncomputable def certificate_1886_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(0,15),(1,2),(1,3),(1,6),(1,7),(1,11),(1,15),(2,3),(2,6),(2,7),(2,11),(2,15),(3,6),(3,7),(3,11),(3,15),(6,7),(6,11),(6,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_1887_q : Finset ℕ := ([0,1,2,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1887_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(1,2),(1,3),(1,6),(1,8),(1,10),(1,13),(2,3),(2,6),(2,8),(2,10),(2,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates060
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1888_q : Finset ℕ := ([0,1,2,3,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1888_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,14),(1,2),(1,3),(1,6),(1,8),(1,10),(1,14),(2,3),(2,6),(2,8),(2,10),(2,14),(3,6),(3,8),(3,10),(3,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1889_q : Finset ℕ := ([0,1,2,3,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_1889_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,15),(1,2),(1,3),(1,6),(1,8),(1,10),(1,15),(2,3),(2,6),(2,8),(2,10),(2,15),(3,6),(3,8),(3,10),(3,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_1890_q : Finset ℕ := ([0,1,2,3,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1890_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(0,14),(1,2),(1,3),(1,6),(1,8),(1,11),(1,14),(2,3),(2,6),(2,8),(2,11),(2,14),(3,6),(3,8),(3,11),(3,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1891_q : Finset ℕ := ([0,1,2,3,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_1891_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(0,15),(1,2),(1,3),(1,6),(1,8),(1,11),(1,15),(2,3),(2,6),(2,8),(2,11),(2,15),(3,6),(3,8),(3,11),(3,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_1892_q : Finset ℕ := ([0,1,2,3,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_1892_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(0,15),(1,2),(1,3),(1,6),(1,8),(1,12),(1,15),(2,3),(2,6),(2,8),(2,12),(2,15),(3,6),(3,8),(3,12),(3,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_1893_q : Finset ℕ := ([0,1,2,3,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1893_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,9),(0,10),(0,14),(1,2),(1,3),(1,6),(1,9),(1,10),(1,14),(2,3),(2,6),(2,9),(2,10),(2,14),(3,6),(3,9),(3,10),(3,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1894_q : Finset ℕ := ([0,1,2,3,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1894_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,9),(0,10),(0,15),(1,2),(1,3),(1,6),(1,9),(1,10),(1,15),(2,3),(2,6),(2,9),(2,10),(2,15),(3,6),(3,9),(3,10),(3,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_1895_q : Finset ℕ := ([0,1,2,3,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1895_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,9),(0,11),(0,15),(1,2),(1,3),(1,6),(1,9),(1,11),(1,15),(2,3),(2,6),(2,9),(2,11),(2,15),(3,6),(3,9),(3,11),(3,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1896_q : Finset ℕ := ([0,1,2,3,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_1896_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,9),(0,12),(0,15),(1,2),(1,3),(1,6),(1,9),(1,12),(1,15),(2,3),(2,6),(2,9),(2,12),(2,15),(3,6),(3,9),(3,12),(3,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_1897_q : Finset ℕ := ([0,1,2,3,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_1897_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,10),(0,11),(0,15),(1,2),(1,3),(1,6),(1,10),(1,11),(1,15),(2,3),(2,6),(2,10),(2,11),(2,15),(3,6),(3,10),(3,11),(3,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_1898_q : Finset ℕ := ([0,1,2,3,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1898_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,7),(0,9),(0,11),(0,15),(1,2),(1,3),(1,7),(1,9),(1,11),(1,15),(2,3),(2,7),(2,9),(2,11),(2,15),(3,7),(3,9),(3,11),(3,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1899_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset
noncomputable def certificate_1899_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_1900_q : Finset ℕ := ([0,1,2,4,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_1900_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,11),(1,2),(1,4),(1,5),(1,7),(1,8),(1,11),(2,4),(2,5),(2,7),(2,8),(2,11),(4,5),(4,7),(4,8),(4,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_1901_q : Finset ℕ := ([0,1,2,4,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_1901_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,12),(1,2),(1,4),(1,5),(1,7),(1,8),(1,12),(2,4),(2,5),(2,7),(2,8),(2,12),(4,5),(4,7),(4,8),(4,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_1902_q : Finset ℕ := ([0,1,2,4,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_1902_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,13),(1,2),(1,4),(1,5),(1,7),(1,8),(1,13),(2,4),(2,5),(2,7),(2,8),(2,13),(4,5),(4,7),(4,8),(4,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_1903_q : Finset ℕ := ([0,1,2,4,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_1903_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,14),(1,2),(1,4),(1,5),(1,7),(1,8),(1,14),(2,4),(2,5),(2,7),(2,8),(2,14),(4,5),(4,7),(4,8),(4,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_1904_q : Finset ℕ := ([0,1,2,4,5,7,8,15] : List ℕ).toFinset
noncomputable def certificate_1904_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,15),(1,2),(1,4),(1,5),(1,7),(1,8),(1,15),(2,4),(2,5),(2,7),(2,8),(2,15),(4,5),(4,7),(4,8),(4,15),(5,7),(5,8),(5,15),(7,8),(7,15),(8,15)]

noncomputable def certificate_1905_q : Finset ℕ := ([0,1,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1905_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(1,2),(1,4),(1,5),(1,7),(1,9),(1,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1906_q : Finset ℕ := ([0,1,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1906_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(1,2),(1,4),(1,5),(1,7),(1,9),(1,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1907_q : Finset ℕ := ([0,1,2,4,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1907_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(1,2),(1,4),(1,5),(1,7),(1,9),(1,13),(2,4),(2,5),(2,7),(2,9),(2,13),(4,5),(4,7),(4,9),(4,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1908_q : Finset ℕ := ([0,1,2,4,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1908_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,14),(1,2),(1,4),(1,5),(1,7),(1,9),(1,14),(2,4),(2,5),(2,7),(2,9),(2,14),(4,5),(4,7),(4,9),(4,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1909_q : Finset ℕ := ([0,1,2,4,5,7,9,15] : List ℕ).toFinset
noncomputable def certificate_1909_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,15),(1,2),(1,4),(1,5),(1,7),(1,9),(1,15),(2,4),(2,5),(2,7),(2,9),(2,15),(4,5),(4,7),(4,9),(4,15),(5,7),(5,9),(5,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_1910_q : Finset ℕ := ([0,1,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1910_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(1,2),(1,4),(1,5),(1,7),(1,10),(1,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1911_q : Finset ℕ := ([0,1,2,4,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1911_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(1,2),(1,4),(1,5),(1,7),(1,10),(1,13),(2,4),(2,5),(2,7),(2,10),(2,13),(4,5),(4,7),(4,10),(4,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1912_q : Finset ℕ := ([0,1,2,4,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1912_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,14),(1,2),(1,4),(1,5),(1,7),(1,10),(1,14),(2,4),(2,5),(2,7),(2,10),(2,14),(4,5),(4,7),(4,10),(4,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1913_q : Finset ℕ := ([0,1,2,4,5,7,10,15] : List ℕ).toFinset
noncomputable def certificate_1913_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,15),(1,2),(1,4),(1,5),(1,7),(1,10),(1,15),(2,4),(2,5),(2,7),(2,10),(2,15),(4,5),(4,7),(4,10),(4,15),(5,7),(5,10),(5,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_1914_q : Finset ℕ := ([0,1,2,4,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1914_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(1,2),(1,4),(1,5),(1,7),(1,11),(1,13),(2,4),(2,5),(2,7),(2,11),(2,13),(4,5),(4,7),(4,11),(4,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1915_q : Finset ℕ := ([0,1,2,4,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_1915_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,14),(1,2),(1,4),(1,5),(1,7),(1,11),(1,14),(2,4),(2,5),(2,7),(2,11),(2,14),(4,5),(4,7),(4,11),(4,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_1916_q : Finset ℕ := ([0,1,2,4,5,7,11,15] : List ℕ).toFinset
noncomputable def certificate_1916_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,15),(1,2),(1,4),(1,5),(1,7),(1,11),(1,15),(2,4),(2,5),(2,7),(2,11),(2,15),(4,5),(4,7),(4,11),(4,15),(5,7),(5,11),(5,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_1917_q : Finset ℕ := ([0,1,2,4,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_1917_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(0,14),(1,2),(1,4),(1,5),(1,7),(1,12),(1,14),(2,4),(2,5),(2,7),(2,12),(2,14),(4,5),(4,7),(4,12),(4,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_1918_q : Finset ℕ := ([0,1,2,4,5,7,12,15] : List ℕ).toFinset
noncomputable def certificate_1918_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(0,15),(1,2),(1,4),(1,5),(1,7),(1,12),(1,15),(2,4),(2,5),(2,7),(2,12),(2,15),(4,5),(4,7),(4,12),(4,15),(5,7),(5,12),(5,15),(7,12),(7,15),(12,15)]

noncomputable def certificate_1919_q : Finset ℕ := ([0,1,2,4,5,7,13,15] : List ℕ).toFinset
noncomputable def certificate_1919_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,13),(0,15),(1,2),(1,4),(1,5),(1,7),(1,13),(1,15),(2,4),(2,5),(2,7),(2,13),(2,15),(4,5),(4,7),(4,13),(4,15),(5,7),(5,13),(5,15),(7,13),(7,15),(13,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates061
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1920_q : Finset ℕ := ([0,1,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1920_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(1,2),(1,4),(1,5),(1,8),(1,9),(1,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1921_q : Finset ℕ := ([0,1,2,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1921_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,13),(1,2),(1,4),(1,5),(1,8),(1,9),(1,13),(2,4),(2,5),(2,8),(2,9),(2,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1922_q : Finset ℕ := ([0,1,2,4,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1922_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,14),(1,2),(1,4),(1,5),(1,8),(1,9),(1,14),(2,4),(2,5),(2,8),(2,9),(2,14),(4,5),(4,8),(4,9),(4,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1923_q : Finset ℕ := ([0,1,2,4,5,8,9,15] : List ℕ).toFinset
noncomputable def certificate_1923_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,15),(1,2),(1,4),(1,5),(1,8),(1,9),(1,15),(2,4),(2,5),(2,8),(2,9),(2,15),(4,5),(4,8),(4,9),(4,15),(5,8),(5,9),(5,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_1924_q : Finset ℕ := ([0,1,2,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1924_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(1,2),(1,4),(1,5),(1,8),(1,10),(1,13),(2,4),(2,5),(2,8),(2,10),(2,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1925_q : Finset ℕ := ([0,1,2,4,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1925_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,14),(1,2),(1,4),(1,5),(1,8),(1,10),(1,14),(2,4),(2,5),(2,8),(2,10),(2,14),(4,5),(4,8),(4,10),(4,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1926_q : Finset ℕ := ([0,1,2,4,5,8,10,15] : List ℕ).toFinset
noncomputable def certificate_1926_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,15),(1,2),(1,4),(1,5),(1,8),(1,10),(1,15),(2,4),(2,5),(2,8),(2,10),(2,15),(4,5),(4,8),(4,10),(4,15),(5,8),(5,10),(5,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_1927_q : Finset ℕ := ([0,1,2,4,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1927_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(0,14),(1,2),(1,4),(1,5),(1,8),(1,11),(1,14),(2,4),(2,5),(2,8),(2,11),(2,14),(4,5),(4,8),(4,11),(4,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1928_q : Finset ℕ := ([0,1,2,4,5,8,11,15] : List ℕ).toFinset
noncomputable def certificate_1928_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(0,15),(1,2),(1,4),(1,5),(1,8),(1,11),(1,15),(2,4),(2,5),(2,8),(2,11),(2,15),(4,5),(4,8),(4,11),(4,15),(5,8),(5,11),(5,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_1929_q : Finset ℕ := ([0,1,2,4,5,8,12,15] : List ℕ).toFinset
noncomputable def certificate_1929_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,12),(0,15),(1,2),(1,4),(1,5),(1,8),(1,12),(1,15),(2,4),(2,5),(2,8),(2,12),(2,15),(4,5),(4,8),(4,12),(4,15),(5,8),(5,12),(5,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_1930_q : Finset ℕ := ([0,1,2,4,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1930_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,9),(0,10),(0,14),(1,2),(1,4),(1,5),(1,9),(1,10),(1,14),(2,4),(2,5),(2,9),(2,10),(2,14),(4,5),(4,9),(4,10),(4,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1931_q : Finset ℕ := ([0,1,2,4,5,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1931_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,9),(0,10),(0,15),(1,2),(1,4),(1,5),(1,9),(1,10),(1,15),(2,4),(2,5),(2,9),(2,10),(2,15),(4,5),(4,9),(4,10),(4,15),(5,9),(5,10),(5,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_1932_q : Finset ℕ := ([0,1,2,4,5,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1932_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,9),(0,11),(0,15),(1,2),(1,4),(1,5),(1,9),(1,11),(1,15),(2,4),(2,5),(2,9),(2,11),(2,15),(4,5),(4,9),(4,11),(4,15),(5,9),(5,11),(5,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1933_q : Finset ℕ := ([0,1,2,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1933_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(1,2),(1,4),(1,6),(1,7),(1,9),(1,11),(2,4),(2,6),(2,7),(2,9),(2,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1934_q : Finset ℕ := ([0,1,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1934_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(1,2),(1,4),(1,6),(1,7),(1,9),(1,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1935_q : Finset ℕ := ([0,1,2,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1935_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(1,2),(1,4),(1,6),(1,7),(1,9),(1,13),(2,4),(2,6),(2,7),(2,9),(2,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1936_q : Finset ℕ := ([0,1,2,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_1936_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,14),(1,2),(1,4),(1,6),(1,7),(1,9),(1,14),(2,4),(2,6),(2,7),(2,9),(2,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_1937_q : Finset ℕ := ([0,1,2,4,6,7,9,15] : List ℕ).toFinset
noncomputable def certificate_1937_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,15),(1,2),(1,4),(1,6),(1,7),(1,9),(1,15),(2,4),(2,6),(2,7),(2,9),(2,15),(4,6),(4,7),(4,9),(4,15),(6,7),(6,9),(6,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_1938_q : Finset ℕ := ([0,1,2,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1938_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(1,2),(1,4),(1,6),(1,7),(1,10),(1,13),(2,4),(2,6),(2,7),(2,10),(2,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1939_q : Finset ℕ := ([0,1,2,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_1939_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,14),(1,2),(1,4),(1,6),(1,7),(1,10),(1,14),(2,4),(2,6),(2,7),(2,10),(2,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_1940_q : Finset ℕ := ([0,1,2,4,6,7,10,15] : List ℕ).toFinset
noncomputable def certificate_1940_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,15),(1,2),(1,4),(1,6),(1,7),(1,10),(1,15),(2,4),(2,6),(2,7),(2,10),(2,15),(4,6),(4,7),(4,10),(4,15),(6,7),(6,10),(6,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_1941_q : Finset ℕ := ([0,1,2,4,6,7,11,15] : List ℕ).toFinset
noncomputable def certificate_1941_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(0,15),(1,2),(1,4),(1,6),(1,7),(1,11),(1,15),(2,4),(2,6),(2,7),(2,11),(2,15),(4,6),(4,7),(4,11),(4,15),(6,7),(6,11),(6,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_1942_q : Finset ℕ := ([0,1,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1942_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(1,2),(1,4),(1,6),(1,8),(1,9),(1,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1943_q : Finset ℕ := ([0,1,2,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1943_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,13),(1,2),(1,4),(1,6),(1,8),(1,9),(1,13),(2,4),(2,6),(2,8),(2,9),(2,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1944_q : Finset ℕ := ([0,1,2,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_1944_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,14),(1,2),(1,4),(1,6),(1,8),(1,9),(1,14),(2,4),(2,6),(2,8),(2,9),(2,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_1945_q : Finset ℕ := ([0,1,2,4,6,8,9,15] : List ℕ).toFinset
noncomputable def certificate_1945_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,15),(1,2),(1,4),(1,6),(1,8),(1,9),(1,15),(2,4),(2,6),(2,8),(2,9),(2,15),(4,6),(4,8),(4,9),(4,15),(6,8),(6,9),(6,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_1946_q : Finset ℕ := ([0,1,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_1946_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(1,2),(1,4),(1,6),(1,8),(1,10),(1,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_1947_q : Finset ℕ := ([0,1,2,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1947_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(1,2),(1,4),(1,6),(1,8),(1,10),(1,13),(2,4),(2,6),(2,8),(2,10),(2,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1948_q : Finset ℕ := ([0,1,2,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1948_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,14),(1,2),(1,4),(1,6),(1,8),(1,10),(1,14),(2,4),(2,6),(2,8),(2,10),(2,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1949_q : Finset ℕ := ([0,1,2,4,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_1949_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,15),(1,2),(1,4),(1,6),(1,8),(1,10),(1,15),(2,4),(2,6),(2,8),(2,10),(2,15),(4,6),(4,8),(4,10),(4,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_1950_q : Finset ℕ := ([0,1,2,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1950_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(1,2),(1,4),(1,6),(1,8),(1,11),(1,13),(2,4),(2,6),(2,8),(2,11),(2,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1951_q : Finset ℕ := ([0,1,2,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1951_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,14),(1,2),(1,4),(1,6),(1,8),(1,11),(1,14),(2,4),(2,6),(2,8),(2,11),(2,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates062
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1952_q : Finset ℕ := ([0,1,2,4,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_1952_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,15),(1,2),(1,4),(1,6),(1,8),(1,11),(1,15),(2,4),(2,6),(2,8),(2,11),(2,15),(4,6),(4,8),(4,11),(4,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_1953_q : Finset ℕ := ([0,1,2,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_1953_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(0,14),(1,2),(1,4),(1,6),(1,8),(1,12),(1,14),(2,4),(2,6),(2,8),(2,12),(2,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_1954_q : Finset ℕ := ([0,1,2,4,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_1954_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(0,15),(1,2),(1,4),(1,6),(1,8),(1,12),(1,15),(2,4),(2,6),(2,8),(2,12),(2,15),(4,6),(4,8),(4,12),(4,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_1955_q : Finset ℕ := ([0,1,2,4,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_1955_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,13),(0,15),(1,2),(1,4),(1,6),(1,8),(1,13),(1,15),(2,4),(2,6),(2,8),(2,13),(2,15),(4,6),(4,8),(4,13),(4,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_1956_q : Finset ℕ := ([0,1,2,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1956_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(1,2),(1,4),(1,6),(1,9),(1,10),(1,13),(2,4),(2,6),(2,9),(2,10),(2,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1957_q : Finset ℕ := ([0,1,2,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1957_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,14),(1,2),(1,4),(1,6),(1,9),(1,10),(1,14),(2,4),(2,6),(2,9),(2,10),(2,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1958_q : Finset ℕ := ([0,1,2,4,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1958_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,15),(1,2),(1,4),(1,6),(1,9),(1,10),(1,15),(2,4),(2,6),(2,9),(2,10),(2,15),(4,6),(4,9),(4,10),(4,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_1959_q : Finset ℕ := ([0,1,2,4,6,9,11,13] : List ℕ).toFinset
noncomputable def certificate_1959_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(1,2),(1,4),(1,6),(1,9),(1,11),(1,13),(2,4),(2,6),(2,9),(2,11),(2,13),(4,6),(4,9),(4,11),(4,13),(6,9),(6,11),(6,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_1960_q : Finset ℕ := ([0,1,2,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1960_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,14),(1,2),(1,4),(1,6),(1,9),(1,11),(1,14),(2,4),(2,6),(2,9),(2,11),(2,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1961_q : Finset ℕ := ([0,1,2,4,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1961_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,15),(1,2),(1,4),(1,6),(1,9),(1,11),(1,15),(2,4),(2,6),(2,9),(2,11),(2,15),(4,6),(4,9),(4,11),(4,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1962_q : Finset ℕ := ([0,1,2,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1962_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(0,14),(1,2),(1,4),(1,6),(1,9),(1,12),(1,14),(2,4),(2,6),(2,9),(2,12),(2,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1963_q : Finset ℕ := ([0,1,2,4,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_1963_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(0,15),(1,2),(1,4),(1,6),(1,9),(1,12),(1,15),(2,4),(2,6),(2,9),(2,12),(2,15),(4,6),(4,9),(4,12),(4,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_1964_q : Finset ℕ := ([0,1,2,4,6,9,13,15] : List ℕ).toFinset
noncomputable def certificate_1964_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,13),(0,15),(1,2),(1,4),(1,6),(1,9),(1,13),(1,15),(2,4),(2,6),(2,9),(2,13),(2,15),(4,6),(4,9),(4,13),(4,15),(6,9),(6,13),(6,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_1965_q : Finset ℕ := ([0,1,2,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1965_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,14),(1,2),(1,4),(1,6),(1,10),(1,11),(1,14),(2,4),(2,6),(2,10),(2,11),(2,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1966_q : Finset ℕ := ([0,1,2,4,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_1966_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,15),(1,2),(1,4),(1,6),(1,10),(1,11),(1,15),(2,4),(2,6),(2,10),(2,11),(2,15),(4,6),(4,10),(4,11),(4,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_1967_q : Finset ℕ := ([0,1,2,4,6,10,12,14] : List ℕ).toFinset
noncomputable def certificate_1967_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(0,14),(1,2),(1,4),(1,6),(1,10),(1,12),(1,14),(2,4),(2,6),(2,10),(2,12),(2,14),(4,6),(4,10),(4,12),(4,14),(6,10),(6,12),(6,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_1968_q : Finset ℕ := ([0,1,2,4,6,10,12,15] : List ℕ).toFinset
noncomputable def certificate_1968_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(0,15),(1,2),(1,4),(1,6),(1,10),(1,12),(1,15),(2,4),(2,6),(2,10),(2,12),(2,15),(4,6),(4,10),(4,12),(4,15),(6,10),(6,12),(6,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_1969_q : Finset ℕ := ([0,1,2,4,6,10,13,15] : List ℕ).toFinset
noncomputable def certificate_1969_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,10),(0,13),(0,15),(1,2),(1,4),(1,6),(1,10),(1,13),(1,15),(2,4),(2,6),(2,10),(2,13),(2,15),(4,6),(4,10),(4,13),(4,15),(6,10),(6,13),(6,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_1970_q : Finset ℕ := ([0,1,2,4,6,11,12,15] : List ℕ).toFinset
noncomputable def certificate_1970_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,11),(0,12),(0,15),(1,2),(1,4),(1,6),(1,11),(1,12),(1,15),(2,4),(2,6),(2,11),(2,12),(2,15),(4,6),(4,11),(4,12),(4,15),(6,11),(6,12),(6,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_1971_q : Finset ℕ := ([0,1,2,4,6,11,13,15] : List ℕ).toFinset
noncomputable def certificate_1971_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,11),(0,13),(0,15),(1,2),(1,4),(1,6),(1,11),(1,13),(1,15),(2,4),(2,6),(2,11),(2,13),(2,15),(4,6),(4,11),(4,13),(4,15),(6,11),(6,13),(6,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_1972_q : Finset ℕ := ([0,1,2,4,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1972_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(1,2),(1,4),(1,7),(1,8),(1,10),(1,13),(2,4),(2,7),(2,8),(2,10),(2,13),(4,7),(4,8),(4,10),(4,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1973_q : Finset ℕ := ([0,1,2,4,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_1973_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,14),(1,2),(1,4),(1,7),(1,8),(1,10),(1,14),(2,4),(2,7),(2,8),(2,10),(2,14),(4,7),(4,8),(4,10),(4,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_1974_q : Finset ℕ := ([0,1,2,4,7,8,10,15] : List ℕ).toFinset
noncomputable def certificate_1974_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,15),(1,2),(1,4),(1,7),(1,8),(1,10),(1,15),(2,4),(2,7),(2,8),(2,10),(2,15),(4,7),(4,8),(4,10),(4,15),(7,8),(7,10),(7,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_1975_q : Finset ℕ := ([0,1,2,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_1975_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(0,14),(1,2),(1,4),(1,7),(1,8),(1,11),(1,14),(2,4),(2,7),(2,8),(2,11),(2,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_1976_q : Finset ℕ := ([0,1,2,4,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_1976_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(0,15),(1,2),(1,4),(1,7),(1,8),(1,11),(1,15),(2,4),(2,7),(2,8),(2,11),(2,15),(4,7),(4,8),(4,11),(4,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_1977_q : Finset ℕ := ([0,1,2,4,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1977_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(1,2),(1,4),(1,7),(1,9),(1,10),(1,13),(2,4),(2,7),(2,9),(2,10),(2,13),(4,7),(4,9),(4,10),(4,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1978_q : Finset ℕ := ([0,1,2,4,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1978_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,14),(1,2),(1,4),(1,7),(1,9),(1,10),(1,14),(2,4),(2,7),(2,9),(2,10),(2,14),(4,7),(4,9),(4,10),(4,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1979_q : Finset ℕ := ([0,1,2,4,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1979_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,15),(1,2),(1,4),(1,7),(1,9),(1,10),(1,15),(2,4),(2,7),(2,9),(2,10),(2,15),(4,7),(4,9),(4,10),(4,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_1980_q : Finset ℕ := ([0,1,2,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_1980_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,11),(0,14),(1,2),(1,4),(1,7),(1,9),(1,11),(1,14),(2,4),(2,7),(2,9),(2,11),(2,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_1981_q : Finset ℕ := ([0,1,2,4,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1981_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,11),(0,15),(1,2),(1,4),(1,7),(1,9),(1,11),(1,15),(2,4),(2,7),(2,9),(2,11),(2,15),(4,7),(4,9),(4,11),(4,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1982_q : Finset ℕ := ([0,1,2,4,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_1982_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(0,14),(1,2),(1,4),(1,7),(1,9),(1,12),(1,14),(2,4),(2,7),(2,9),(2,12),(2,14),(4,7),(4,9),(4,12),(4,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_1983_q : Finset ℕ := ([0,1,2,4,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_1983_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(0,15),(1,2),(1,4),(1,7),(1,9),(1,12),(1,15),(2,4),(2,7),(2,9),(2,12),(2,15),(4,7),(4,9),(4,12),(4,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates063
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1984_q : Finset ℕ := ([0,1,2,4,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_1984_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,13),(0,15),(1,2),(1,4),(1,7),(1,9),(1,13),(1,15),(2,4),(2,7),(2,9),(2,13),(2,15),(4,7),(4,9),(4,13),(4,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_1985_q : Finset ℕ := ([0,1,2,4,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1985_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,10),(0,11),(0,14),(1,2),(1,4),(1,7),(1,10),(1,11),(1,14),(2,4),(2,7),(2,10),(2,11),(2,14),(4,7),(4,10),(4,11),(4,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1986_q : Finset ℕ := ([0,1,2,4,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_1986_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,10),(0,11),(0,15),(1,2),(1,4),(1,7),(1,10),(1,11),(1,15),(2,4),(2,7),(2,10),(2,11),(2,15),(4,7),(4,10),(4,11),(4,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_1987_q : Finset ℕ := ([0,1,2,4,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_1987_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,10),(0,12),(0,15),(1,2),(1,4),(1,7),(1,10),(1,12),(1,15),(2,4),(2,7),(2,10),(2,12),(2,15),(4,7),(4,10),(4,12),(4,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_1988_q : Finset ℕ := ([0,1,2,4,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_1988_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,10),(0,13),(0,15),(1,2),(1,4),(1,7),(1,10),(1,13),(1,15),(2,4),(2,7),(2,10),(2,13),(2,15),(4,7),(4,10),(4,13),(4,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_1989_q : Finset ℕ := ([0,1,2,4,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_1989_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,11),(0,12),(0,15),(1,2),(1,4),(1,7),(1,11),(1,12),(1,15),(2,4),(2,7),(2,11),(2,12),(2,15),(4,7),(4,11),(4,12),(4,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_1990_q : Finset ℕ := ([0,1,2,4,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_1990_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,9),(0,11),(0,15),(1,2),(1,4),(1,8),(1,9),(1,11),(1,15),(2,4),(2,8),(2,9),(2,11),(2,15),(4,8),(4,9),(4,11),(4,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_1991_q : Finset ℕ := ([0,1,2,4,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_1991_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,9),(0,12),(0,15),(1,2),(1,4),(1,8),(1,9),(1,12),(1,15),(2,4),(2,8),(2,9),(2,12),(2,15),(4,8),(4,9),(4,12),(4,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_1992_q : Finset ℕ := ([0,1,2,4,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_1992_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,8),(0,10),(0,11),(0,14),(1,2),(1,4),(1,8),(1,10),(1,11),(1,14),(2,4),(2,8),(2,10),(2,11),(2,14),(4,8),(4,10),(4,11),(4,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_1993_q : Finset ℕ := ([0,1,2,4,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_1993_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,10),(0,11),(0,15),(1,2),(1,4),(1,8),(1,10),(1,11),(1,15),(2,4),(2,8),(2,10),(2,11),(2,15),(4,8),(4,10),(4,11),(4,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_1994_q : Finset ℕ := ([0,1,2,4,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_1994_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,10),(0,12),(0,15),(1,2),(1,4),(1,8),(1,10),(1,12),(1,15),(2,4),(2,8),(2,10),(2,12),(2,15),(4,8),(4,10),(4,12),(4,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_1995_q : Finset ℕ := ([0,1,2,4,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_1995_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,8),(0,11),(0,12),(0,15),(1,2),(1,4),(1,8),(1,11),(1,12),(1,15),(2,4),(2,8),(2,11),(2,12),(2,15),(4,8),(4,11),(4,12),(4,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_1996_q : Finset ℕ := ([0,1,2,4,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_1996_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,9),(0,11),(0,12),(0,15),(1,2),(1,4),(1,9),(1,11),(1,12),(1,15),(2,4),(2,9),(2,11),(2,12),(2,15),(4,9),(4,11),(4,12),(4,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_1997_q : Finset ℕ := ([0,1,2,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1997_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,13),(1,2),(1,5),(1,6),(1,9),(1,10),(1,13),(2,5),(2,6),(2,9),(2,10),(2,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1998_q : Finset ℕ := ([0,1,2,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_1998_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,14),(1,2),(1,5),(1,6),(1,9),(1,10),(1,14),(2,5),(2,6),(2,9),(2,10),(2,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_1999_q : Finset ℕ := ([0,1,2,5,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_1999_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,9),(0,10),(0,15),(1,2),(1,5),(1,6),(1,9),(1,10),(1,15),(2,5),(2,6),(2,9),(2,10),(2,15),(5,6),(5,9),(5,10),(5,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2000_q : Finset ℕ := ([0,1,2,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2000_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,6),(0,9),(0,11),(0,14),(1,2),(1,5),(1,6),(1,9),(1,11),(1,14),(2,5),(2,6),(2,9),(2,11),(2,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2001_q : Finset ℕ := ([0,1,2,5,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2001_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,9),(0,11),(0,15),(1,2),(1,5),(1,6),(1,9),(1,11),(1,15),(2,5),(2,6),(2,9),(2,11),(2,15),(5,6),(5,9),(5,11),(5,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2002_q : Finset ℕ := ([0,1,2,5,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2002_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,9),(0,12),(0,15),(1,2),(1,5),(1,6),(1,9),(1,12),(1,15),(2,5),(2,6),(2,9),(2,12),(2,15),(5,6),(5,9),(5,12),(5,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2003_q : Finset ℕ := ([0,1,2,5,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2003_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,6),(0,10),(0,11),(0,15),(1,2),(1,5),(1,6),(1,10),(1,11),(1,15),(2,5),(2,6),(2,10),(2,11),(2,15),(5,6),(5,10),(5,11),(5,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2004_q : Finset ℕ := ([0,1,2,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2004_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,5),(0,7),(0,9),(0,11),(0,14),(1,2),(1,5),(1,7),(1,9),(1,11),(1,14),(2,5),(2,7),(2,9),(2,11),(2,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2005_q : Finset ℕ := ([0,1,2,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2005_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,9),(0,11),(0,15),(1,2),(1,5),(1,7),(1,9),(1,11),(1,15),(2,5),(2,7),(2,9),(2,11),(2,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2006_q : Finset ℕ := ([0,1,2,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2006_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,9),(0,12),(0,15),(1,2),(1,5),(1,7),(1,9),(1,12),(1,15),(2,5),(2,7),(2,9),(2,12),(2,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2007_q : Finset ℕ := ([0,1,2,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2007_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,10),(0,11),(0,15),(1,2),(1,5),(1,7),(1,10),(1,11),(1,15),(2,5),(2,7),(2,10),(2,11),(2,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2008_q : Finset ℕ := ([0,1,2,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2008_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,7),(0,10),(0,12),(0,15),(1,2),(1,5),(1,7),(1,10),(1,12),(1,15),(2,5),(2,7),(2,10),(2,12),(2,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2009_q : Finset ℕ := ([0,1,2,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2009_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,5),(0,8),(0,9),(0,12),(0,15),(1,2),(1,5),(1,8),(1,9),(1,12),(1,15),(2,5),(2,8),(2,9),(2,12),(2,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2010_q : Finset ℕ := ([0,1,3,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_2010_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,11),(1,3),(1,4),(1,6),(1,7),(1,9),(1,11),(3,4),(3,6),(3,7),(3,9),(3,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_2011_q : Finset ℕ := ([0,1,3,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_2011_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,12),(1,3),(1,4),(1,6),(1,7),(1,9),(1,12),(3,4),(3,6),(3,7),(3,9),(3,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_2012_q : Finset ℕ := ([0,1,3,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_2012_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,13),(1,3),(1,4),(1,6),(1,7),(1,9),(1,13),(3,4),(3,6),(3,7),(3,9),(3,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_2013_q : Finset ℕ := ([0,1,3,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_2013_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,14),(1,3),(1,4),(1,6),(1,7),(1,9),(1,14),(3,4),(3,6),(3,7),(3,9),(3,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_2014_q : Finset ℕ := ([0,1,3,4,6,7,9,15] : List ℕ).toFinset
noncomputable def certificate_2014_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(0,15),(1,3),(1,4),(1,6),(1,7),(1,9),(1,15),(3,4),(3,6),(3,7),(3,9),(3,15),(4,6),(4,7),(4,9),(4,15),(6,7),(6,9),(6,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_2015_q : Finset ℕ := ([0,1,3,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2015_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,13),(1,3),(1,4),(1,6),(1,7),(1,10),(1,13),(3,4),(3,6),(3,7),(3,10),(3,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates064
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2016_q : Finset ℕ := ([0,1,3,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2016_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,14),(1,3),(1,4),(1,6),(1,7),(1,10),(1,14),(3,4),(3,6),(3,7),(3,10),(3,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2017_q : Finset ℕ := ([0,1,3,4,6,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2017_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,7),(0,10),(0,15),(1,3),(1,4),(1,6),(1,7),(1,10),(1,15),(3,4),(3,6),(3,7),(3,10),(3,15),(4,6),(4,7),(4,10),(4,15),(6,7),(6,10),(6,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2018_q : Finset ℕ := ([0,1,3,4,6,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2018_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,7),(0,11),(0,15),(1,3),(1,4),(1,6),(1,7),(1,11),(1,15),(3,4),(3,6),(3,7),(3,11),(3,15),(4,6),(4,7),(4,11),(4,15),(6,7),(6,11),(6,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2019_q : Finset ℕ := ([0,1,3,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2019_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,12),(1,3),(1,4),(1,6),(1,8),(1,9),(1,12),(3,4),(3,6),(3,8),(3,9),(3,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2020_q : Finset ℕ := ([0,1,3,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2020_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,13),(1,3),(1,4),(1,6),(1,8),(1,9),(1,13),(3,4),(3,6),(3,8),(3,9),(3,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2021_q : Finset ℕ := ([0,1,3,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2021_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,14),(1,3),(1,4),(1,6),(1,8),(1,9),(1,14),(3,4),(3,6),(3,8),(3,9),(3,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2022_q : Finset ℕ := ([0,1,3,4,6,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2022_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,9),(0,15),(1,3),(1,4),(1,6),(1,8),(1,9),(1,15),(3,4),(3,6),(3,8),(3,9),(3,15),(4,6),(4,8),(4,9),(4,15),(6,8),(6,9),(6,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2023_q : Finset ℕ := ([0,1,3,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2023_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,12),(1,3),(1,4),(1,6),(1,8),(1,10),(1,12),(3,4),(3,6),(3,8),(3,10),(3,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2024_q : Finset ℕ := ([0,1,3,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2024_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,13),(1,3),(1,4),(1,6),(1,8),(1,10),(1,13),(3,4),(3,6),(3,8),(3,10),(3,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2025_q : Finset ℕ := ([0,1,3,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2025_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,14),(1,3),(1,4),(1,6),(1,8),(1,10),(1,14),(3,4),(3,6),(3,8),(3,10),(3,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2026_q : Finset ℕ := ([0,1,3,4,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2026_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,10),(0,15),(1,3),(1,4),(1,6),(1,8),(1,10),(1,15),(3,4),(3,6),(3,8),(3,10),(3,15),(4,6),(4,8),(4,10),(4,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2027_q : Finset ℕ := ([0,1,3,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2027_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,13),(1,3),(1,4),(1,6),(1,8),(1,11),(1,13),(3,4),(3,6),(3,8),(3,11),(3,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2028_q : Finset ℕ := ([0,1,3,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2028_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,14),(1,3),(1,4),(1,6),(1,8),(1,11),(1,14),(3,4),(3,6),(3,8),(3,11),(3,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2029_q : Finset ℕ := ([0,1,3,4,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2029_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,11),(0,15),(1,3),(1,4),(1,6),(1,8),(1,11),(1,15),(3,4),(3,6),(3,8),(3,11),(3,15),(4,6),(4,8),(4,11),(4,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2030_q : Finset ℕ := ([0,1,3,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2030_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(0,14),(1,3),(1,4),(1,6),(1,8),(1,12),(1,14),(3,4),(3,6),(3,8),(3,12),(3,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2031_q : Finset ℕ := ([0,1,3,4,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2031_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,12),(0,15),(1,3),(1,4),(1,6),(1,8),(1,12),(1,15),(3,4),(3,6),(3,8),(3,12),(3,15),(4,6),(4,8),(4,12),(4,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2032_q : Finset ℕ := ([0,1,3,4,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2032_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,8),(0,13),(0,15),(1,3),(1,4),(1,6),(1,8),(1,13),(1,15),(3,4),(3,6),(3,8),(3,13),(3,15),(4,6),(4,8),(4,13),(4,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2033_q : Finset ℕ := ([0,1,3,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2033_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,13),(1,3),(1,4),(1,6),(1,9),(1,10),(1,13),(3,4),(3,6),(3,9),(3,10),(3,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2034_q : Finset ℕ := ([0,1,3,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2034_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,14),(1,3),(1,4),(1,6),(1,9),(1,10),(1,14),(3,4),(3,6),(3,9),(3,10),(3,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2035_q : Finset ℕ := ([0,1,3,4,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2035_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,10),(0,15),(1,3),(1,4),(1,6),(1,9),(1,10),(1,15),(3,4),(3,6),(3,9),(3,10),(3,15),(4,6),(4,9),(4,10),(4,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2036_q : Finset ℕ := ([0,1,3,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2036_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(0,14),(1,3),(1,4),(1,6),(1,9),(1,11),(1,14),(3,4),(3,6),(3,9),(3,11),(3,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2037_q : Finset ℕ := ([0,1,3,4,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2037_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,11),(0,15),(1,3),(1,4),(1,6),(1,9),(1,11),(1,15),(3,4),(3,6),(3,9),(3,11),(3,15),(4,6),(4,9),(4,11),(4,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2038_q : Finset ℕ := ([0,1,3,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2038_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(0,14),(1,3),(1,4),(1,6),(1,9),(1,12),(1,14),(3,4),(3,6),(3,9),(3,12),(3,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2039_q : Finset ℕ := ([0,1,3,4,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2039_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,12),(0,15),(1,3),(1,4),(1,6),(1,9),(1,12),(1,15),(3,4),(3,6),(3,9),(3,12),(3,15),(4,6),(4,9),(4,12),(4,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2040_q : Finset ℕ := ([0,1,3,4,6,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2040_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,9),(0,13),(0,15),(1,3),(1,4),(1,6),(1,9),(1,13),(1,15),(3,4),(3,6),(3,9),(3,13),(3,15),(4,6),(4,9),(4,13),(4,15),(6,9),(6,13),(6,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2041_q : Finset ℕ := ([0,1,3,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2041_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,6),(0,10),(0,11),(0,14),(1,3),(1,4),(1,6),(1,10),(1,11),(1,14),(3,4),(3,6),(3,10),(3,11),(3,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2042_q : Finset ℕ := ([0,1,3,4,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2042_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,10),(0,11),(0,15),(1,3),(1,4),(1,6),(1,10),(1,11),(1,15),(3,4),(3,6),(3,10),(3,11),(3,15),(4,6),(4,10),(4,11),(4,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2043_q : Finset ℕ := ([0,1,3,4,6,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2043_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,10),(0,12),(0,15),(1,3),(1,4),(1,6),(1,10),(1,12),(1,15),(3,4),(3,6),(3,10),(3,12),(3,15),(4,6),(4,10),(4,12),(4,15),(6,10),(6,12),(6,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2044_q : Finset ℕ := ([0,1,3,4,6,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2044_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,6),(0,11),(0,12),(0,15),(1,3),(1,4),(1,6),(1,11),(1,12),(1,15),(3,4),(3,6),(3,11),(3,12),(3,15),(4,6),(4,11),(4,12),(4,15),(6,11),(6,12),(6,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2045_q : Finset ℕ := ([0,1,3,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2045_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(0,14),(1,3),(1,4),(1,7),(1,8),(1,11),(1,14),(3,4),(3,7),(3,8),(3,11),(3,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2046_q : Finset ℕ := ([0,1,3,4,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2046_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,8),(0,11),(0,15),(1,3),(1,4),(1,7),(1,8),(1,11),(1,15),(3,4),(3,7),(3,8),(3,11),(3,15),(4,7),(4,8),(4,11),(4,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2047_q : Finset ℕ := ([0,1,3,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2047_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,4),(0,7),(0,9),(0,11),(0,14),(1,3),(1,4),(1,7),(1,9),(1,11),(1,14),(3,4),(3,7),(3,9),(3,11),(3,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates065
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2048_q : Finset ℕ := ([0,1,3,4,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2048_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,9),(0,11),(0,15),(1,3),(1,4),(1,7),(1,9),(1,11),(1,15),(3,4),(3,7),(3,9),(3,11),(3,15),(4,7),(4,9),(4,11),(4,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2049_q : Finset ℕ := ([0,1,3,4,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2049_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,9),(0,12),(0,15),(1,3),(1,4),(1,7),(1,9),(1,12),(1,15),(3,4),(3,7),(3,9),(3,12),(3,15),(4,7),(4,9),(4,12),(4,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2050_q : Finset ℕ := ([0,1,3,4,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2050_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,4),(0,7),(0,10),(0,11),(0,15),(1,3),(1,4),(1,7),(1,10),(1,11),(1,15),(3,4),(3,7),(3,10),(3,11),(3,15),(4,7),(4,10),(4,11),(4,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2051_q : Finset ℕ := ([0,1,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2051_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(1,3),(1,5),(1,6),(1,8),(1,10),(1,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2052_q : Finset ℕ := ([0,1,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2052_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(1,3),(1,5),(1,6),(1,8),(1,10),(1,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2053_q : Finset ℕ := ([0,1,3,5,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2053_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,14),(1,3),(1,5),(1,6),(1,8),(1,10),(1,14),(3,5),(3,6),(3,8),(3,10),(3,14),(5,6),(5,8),(5,10),(5,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2054_q : Finset ℕ := ([0,1,3,5,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2054_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,10),(0,15),(1,3),(1,5),(1,6),(1,8),(1,10),(1,15),(3,5),(3,6),(3,8),(3,10),(3,15),(5,6),(5,8),(5,10),(5,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2055_q : Finset ℕ := ([0,1,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2055_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(1,3),(1,5),(1,6),(1,8),(1,11),(1,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2056_q : Finset ℕ := ([0,1,3,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2056_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,14),(1,3),(1,5),(1,6),(1,8),(1,11),(1,14),(3,5),(3,6),(3,8),(3,11),(3,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2057_q : Finset ℕ := ([0,1,3,5,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2057_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,11),(0,15),(1,3),(1,5),(1,6),(1,8),(1,11),(1,15),(3,5),(3,6),(3,8),(3,11),(3,15),(5,6),(5,8),(5,11),(5,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2058_q : Finset ℕ := ([0,1,3,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2058_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(0,14),(1,3),(1,5),(1,6),(1,8),(1,12),(1,14),(3,5),(3,6),(3,8),(3,12),(3,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2059_q : Finset ℕ := ([0,1,3,5,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2059_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,12),(0,15),(1,3),(1,5),(1,6),(1,8),(1,12),(1,15),(3,5),(3,6),(3,8),(3,12),(3,15),(5,6),(5,8),(5,12),(5,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2060_q : Finset ℕ := ([0,1,3,5,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2060_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,8),(0,13),(0,15),(1,3),(1,5),(1,6),(1,8),(1,13),(1,15),(3,5),(3,6),(3,8),(3,13),(3,15),(5,6),(5,8),(5,13),(5,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2061_q : Finset ℕ := ([0,1,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2061_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(1,3),(1,5),(1,6),(1,9),(1,10),(1,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2062_q : Finset ℕ := ([0,1,3,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2062_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,14),(1,3),(1,5),(1,6),(1,9),(1,10),(1,14),(3,5),(3,6),(3,9),(3,10),(3,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2063_q : Finset ℕ := ([0,1,3,5,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2063_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,9),(0,10),(0,15),(1,3),(1,5),(1,6),(1,9),(1,10),(1,15),(3,5),(3,6),(3,9),(3,10),(3,15),(5,6),(5,9),(5,10),(5,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2064_q : Finset ℕ := ([0,1,3,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2064_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,6),(0,9),(0,11),(0,14),(1,3),(1,5),(1,6),(1,9),(1,11),(1,14),(3,5),(3,6),(3,9),(3,11),(3,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2065_q : Finset ℕ := ([0,1,3,5,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2065_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,9),(0,11),(0,15),(1,3),(1,5),(1,6),(1,9),(1,11),(1,15),(3,5),(3,6),(3,9),(3,11),(3,15),(5,6),(5,9),(5,11),(5,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2066_q : Finset ℕ := ([0,1,3,5,6,9,12,15] : List ℕ).toFinset

end CycleClique

end OAI
end


