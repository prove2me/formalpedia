-- Prove2me | Definitions.Def_OAIQ107D004
-- name    : OAIQ107D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:39:17.928178+00:00
-- url     : https://prove2.me/theorems/47cfc29a-152b-4e90-9e93-2b6b7ad7f6db
-- title:
--   Definitions bundle OAIQ107D004 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1268 declarations of OpenAI's Lean: 1267 definitions and 1 instance. The definitions and types are `OAI.CycleClique.certificate_2066_edges`, `OAI.CycleClique.certificate_2067_edges`, `OAI.CycleClique.certificate_2067_q`, `OAI.CycleClique.certificate_2068_edges`, `OAI.CycleClique.certificate_2068_q`, `OAI.CycleClique.certificate_2069_edges`, `OAI.CycleClique.certificate_2069_q`, `OAI.CycleClique.certificate_206_edges`, `OAI.CycleClique.certificate_206_q`, `OAI.CycleClique.certificate_2070_edges`, `OAI.CycleClique.certificate_2070_q`, `OAI.CycleClique.certificate_2071_edges`, `OAI.CycleClique.certificate_2071_q`, `OAI.CycleClique.certificate_2072_edges`, `OAI.CycleClique.certificate_2072_q`, `OAI.CycleClique.certificate_2073_edges`, `OAI.CycleClique.certificate_2073_q`, `OAI.CycleClique.certificate_2074_edges`, `OAI.CycleClique.certificate_2074_q`, `OAI.CycleClique.certificate_2075_edges`, `OAI.CycleClique.certificate_2075_q`, `OAI.CycleClique.certificate_2076_edges`, `OAI.CycleClique.certificate_2076_q`, `OAI.CycleClique.certificate_2077_edges`, `OAI.CycleClique.certificate_2077_q`, `OAI.CycleClique.certificate_2078_edges`, `OAI.CycleClique.certificate_2078_q`, `OAI.CycleClique.certificate_2079_edges`, `OAI.CycleClique.certificate_2079_q`, `OAI.CycleClique.certificate_207_edges`, `OAI.CycleClique.certificate_207_q`, `OAI.CycleClique.certificate_2080_edges`, `OAI.CycleClique.certificate_2080_q`, `OAI.CycleClique.certificate_2081_edges`, `OAI.CycleClique.certificate_2081_q`, `OAI.CycleClique.certificate_2082_edges`, `OAI.CycleClique.certificate_2082_q`, `OAI.CycleClique.certificate_2083_edges`, `OAI.CycleClique.certificate_2083_q`, `OAI.CycleClique.certificate_2084_edges` and 1227 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates007`, `Ramsey_CycleClique_Certificates008`, `Ramsey_CycleClique_Certificates009`, `Ramsey_CycleClique_Certificates065`, `Ramsey_CycleClique_Certificates066`, `Ramsey_CycleClique_Certificates067`, `Ramsey_CycleClique_Certificates068`, `Ramsey_CycleClique_Certificates069`, `Ramsey_CycleClique_Certificates070`, `Ramsey_CycleClique_Certificates071`, `Ramsey_CycleClique_Certificates072`, `Ramsey_CycleClique_Certificates073`, `Ramsey_CycleClique_Certificates074`, `Ramsey_CycleClique_Certificates075`, `Ramsey_CycleClique_Certificates076`, `Ramsey_CycleClique_Certificates077`, `Ramsey_CycleClique_Certificates078`, `Ramsey_CycleClique_Certificates079`, `Ramsey_CycleClique_Certificates080`, `Ramsey_CycleClique_Certificates081`, `Ramsey_CycleClique_CliqueBits`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D021`, `OAIQ107D022`, `OAIQ107D029`, `OAIQ107D030`, `OAIQ107D041`, `OAIQ107D042`, `OAIQ107D043`, `OAIQ107D046`, `OAIQ107D049`, `OAIQ107D052`, `OAIQ107D053`, `OAIQ107D057`, `OAIQ107D060`, `OAIQ107D061`, `OAIQ107D063`, `OAIQ107D067`, `OAIQ107D068`, `OAIQ107D069`, `OAIQ107D071`, `OAIQ107D072`, `OAIQ107D074`, `OAIQ107D075`, `OAIQ107D076`, `OAIQ107D077`, `OAIQ107D078`, `OAIQ107D082` and `OAIQ107D084`.
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

instance instAssociativeNatLor_solutions : Std.Associative Nat.lor := ⟨Nat.lor_assoc⟩

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

noncomputable def certificate_20_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

noncomputable def certificate_21_q : Finset ℕ := ([0,1,2] : List ℕ).toFinset
noncomputable def certificate_21_edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]

noncomputable def certificate_22_q : Finset ℕ := ([0,1,3] : List ℕ).toFinset
noncomputable def certificate_22_edges : List (ℕ × ℕ) := [(1,2),(2,3),(0,1),(0,3),(1,3)]

noncomputable def certificate_23_q : Finset ℕ := ([0,1,4] : List ℕ).toFinset
noncomputable def certificate_23_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(0,1),(0,4),(1,4)]

noncomputable def certificate_24_q : Finset ℕ := ([0,1,5] : List ℕ).toFinset

noncomputable def certificate_24_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(0,1),(0,5),(1,5)]

noncomputable def certificate_24_E : List (ℕ × ℕ) := certificate_24_edges

noncomputable def certificate_24_part_1_E : List (ℕ × ℕ) := certificate_24_E

noncomputable def certificate_24_part_3_E : List (ℕ × ℕ) := certificate_24_part_1_E

noncomputable def certificate_24_part_4_E : List (ℕ × ℕ) := certificate_24_part_3_E

noncomputable def certificate_24_part_6_E : List (ℕ × ℕ) := certificate_24_part_4_E

noncomputable def certificate_24_part_7_E : List (ℕ × ℕ) := certificate_24_part_6_E

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

noncomputable def certificate_206_q : Finset ℕ := ([0,1,2,3,4,5,9] : List ℕ).toFinset
noncomputable def certificate_206_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(1,2),(1,3),(1,4),(1,5),(1,9),(2,3),(2,4),(2,5),(2,9),(3,4),(3,5),(3,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_207_q : Finset ℕ := ([0,1,2,3,4,6,8] : List ℕ).toFinset
noncomputable def certificate_207_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,6),(2,8),(3,4),(3,6),(3,8),(4,6),(4,8),(6,8)]

noncomputable def certificate_208_q : Finset ℕ := ([0,1,2,3,4,6,9] : List ℕ).toFinset
noncomputable def certificate_208_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(1,2),(1,3),(1,4),(1,6),(1,9),(2,3),(2,4),(2,6),(2,9),(3,4),(3,6),(3,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_209_q : Finset ℕ := ([0,1,2,3,5,6,8] : List ℕ).toFinset
noncomputable def certificate_209_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(1,2),(1,3),(1,5),(1,6),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_210_q : Finset ℕ := ([0,1,2,3,5,6,9] : List ℕ).toFinset
noncomputable def certificate_210_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(1,2),(1,3),(1,5),(1,6),(1,9),(2,3),(2,5),(2,6),(2,9),(3,5),(3,6),(3,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_211_q : Finset ℕ := ([0,1,2,3,5,7,9] : List ℕ).toFinset
noncomputable def certificate_211_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(1,2),(1,3),(1,5),(1,7),(1,9),(2,3),(2,5),(2,7),(2,9),(3,5),(3,7),(3,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_212_q : Finset ℕ := ([0,1,2,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_212_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(1,2),(1,4),(1,5),(1,7),(1,9),(2,4),(2,5),(2,7),(2,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_213_q : Finset ℕ := ([0,1,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_213_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(7,8),(8,9),(0,1),(0,3),(0,4),(0,6),(0,7),(0,9),(1,3),(1,4),(1,6),(1,7),(1,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_214_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_214_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_215_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_215_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_216_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_216_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_217_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_217_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_218_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_218_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_219_q : Finset ℕ := ([0,1,2,3,4] : List ℕ).toFinset
noncomputable def certificate_219_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

noncomputable def certificate_220_q : Finset ℕ := ([0,1,2,3,5] : List ℕ).toFinset
noncomputable def certificate_220_edges : List (ℕ × ℕ) := [(3,4),(4,5),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)]

noncomputable def certificate_221_q : Finset ℕ := ([0,1,2,3,6] : List ℕ).toFinset
noncomputable def certificate_221_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(0,1),(0,2),(0,3),(0,6),(1,2),(1,3),(1,6),(2,3),(2,6),(3,6)]

noncomputable def certificate_222_q : Finset ℕ := ([0,1,2,3,7] : List ℕ).toFinset
noncomputable def certificate_222_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,3),(0,7),(1,2),(1,3),(1,7),(2,3),(2,7),(3,7)]

noncomputable def certificate_223_q : Finset ℕ := ([0,1,2,3,8] : List ℕ).toFinset
noncomputable def certificate_223_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,3),(0,8),(1,2),(1,3),(1,8),(2,3),(2,8),(3,8)]

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

noncomputable def certificate_224_q : Finset ℕ := ([0,1,2,3,9] : List ℕ).toFinset

noncomputable def certificate_224_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,9),(1,2),(1,3),(1,9),(2,3),(2,9),(3,9)]

noncomputable def certificate_224_E : List (ℕ × ℕ) := certificate_224_edges

noncomputable def certificate_224_part_1_E : List (ℕ × ℕ) := certificate_224_E

noncomputable def certificate_224_part_2_E : List (ℕ × ℕ) := certificate_224_part_1_E

noncomputable def certificate_224_part_3_E : List (ℕ × ℕ) := certificate_224_part_2_E

noncomputable def certificate_224_part_4_E : List (ℕ × ℕ) := certificate_224_part_3_E

noncomputable def certificate_224_part_6_E : List (ℕ × ℕ) := certificate_224_part_4_E

noncomputable def certificate_224_part_7_E : List (ℕ × ℕ) := certificate_224_part_6_E

noncomputable def certificate_224_part_14_E : List (ℕ × ℕ) := certificate_224_part_7_E

noncomputable def certificate_224_part_19_E : List (ℕ × ℕ) := certificate_224_part_14_E

noncomputable def certificate_225_q : Finset ℕ := ([0,1,2,3,10] : List ℕ).toFinset

noncomputable def certificate_225_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,10),(1,2),(1,3),(1,10),(2,3),(2,10),(3,10)]

noncomputable def certificate_225_E : List (ℕ × ℕ) := certificate_225_edges

noncomputable def certificate_225_part_1_E : List (ℕ × ℕ) := certificate_225_E

noncomputable def certificate_225_part_2_E : List (ℕ × ℕ) := certificate_225_part_1_E

noncomputable def certificate_225_part_3_E : List (ℕ × ℕ) := certificate_225_part_2_E

noncomputable def certificate_225_part_4_E : List (ℕ × ℕ) := certificate_225_part_3_E

noncomputable def certificate_225_part_5_E : List (ℕ × ℕ) := certificate_225_part_4_E

noncomputable def certificate_225_part_8_E : List (ℕ × ℕ) := certificate_225_part_5_E

noncomputable def certificate_225_part_12_E : List (ℕ × ℕ) := certificate_225_part_8_E

noncomputable def certificate_225_part_13_E : List (ℕ × ℕ) := certificate_225_part_12_E

noncomputable def certificate_225_part_15_E : List (ℕ × ℕ) := certificate_225_part_13_E

noncomputable def certificate_225_part_19_E : List (ℕ × ℕ) := certificate_225_part_15_E

noncomputable def certificate_225_part_20_E : List (ℕ × ℕ) := certificate_225_part_19_E

noncomputable def certificate_225_part_25_E : List (ℕ × ℕ) := certificate_225_part_20_E

noncomputable def certificate_225_part_37_E : List (ℕ × ℕ) := certificate_225_part_25_E

noncomputable def certificate_225_part_44_E : List (ℕ × ℕ) := certificate_225_part_37_E

noncomputable def certificate_225_part_48_E : List (ℕ × ℕ) := certificate_225_part_44_E

noncomputable def certificate_225_part_52_E : List (ℕ × ℕ) := certificate_225_part_48_E

noncomputable def certificate_225_part_53_E : List (ℕ × ℕ) := certificate_225_part_52_E

noncomputable def certificate_225_part_58_E : List (ℕ × ℕ) := certificate_225_part_53_E

noncomputable def certificate_225_part_76_E : List (ℕ × ℕ) := certificate_225_part_58_E

noncomputable def certificate_225_part_83_E : List (ℕ × ℕ) := certificate_225_part_76_E

noncomputable def certificate_226_q : Finset ℕ := ([0,1,2,4,6] : List ℕ).toFinset
noncomputable def certificate_226_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(0,1),(0,2),(0,4),(0,6),(1,2),(1,4),(1,6),(2,4),(2,6),(4,6)]

noncomputable def certificate_227_q : Finset ℕ := ([0,1,2,4,7] : List ℕ).toFinset
noncomputable def certificate_227_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,2),(0,4),(0,7),(1,2),(1,4),(1,7),(2,4),(2,7),(4,7)]

noncomputable def certificate_228_q : Finset ℕ := ([0,1,2,4,8] : List ℕ).toFinset
noncomputable def certificate_228_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,4),(0,8),(1,2),(1,4),(1,8),(2,4),(2,8),(4,8)]

noncomputable def certificate_229_q : Finset ℕ := ([0,1,2,4,9] : List ℕ).toFinset
noncomputable def certificate_229_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,4),(0,9),(1,2),(1,4),(1,9),(2,4),(2,9),(4,9)]

noncomputable def certificate_230_q : Finset ℕ := ([0,1,2,4,10] : List ℕ).toFinset

noncomputable def certificate_230_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,4),(0,10),(1,2),(1,4),(1,10),(2,4),(2,10),(4,10)]

noncomputable def certificate_230_E : List (ℕ × ℕ) := certificate_230_edges

noncomputable def certificate_230_part_1_E : List (ℕ × ℕ) := certificate_230_E

noncomputable def certificate_230_part_2_E : List (ℕ × ℕ) := certificate_230_part_1_E

noncomputable def certificate_230_part_3_E : List (ℕ × ℕ) := certificate_230_part_2_E

noncomputable def certificate_230_part_4_E : List (ℕ × ℕ) := certificate_230_part_3_E

noncomputable def certificate_230_part_5_E : List (ℕ × ℕ) := certificate_230_part_4_E

noncomputable def certificate_230_part_7_E : List (ℕ × ℕ) := certificate_230_part_5_E

noncomputable def certificate_230_part_8_E : List (ℕ × ℕ) := certificate_230_part_7_E

noncomputable def certificate_230_part_15_E : List (ℕ × ℕ) := certificate_230_part_8_E

noncomputable def certificate_230_part_23_E : List (ℕ × ℕ) := certificate_230_part_15_E

noncomputable def certificate_230_part_25_E : List (ℕ × ℕ) := certificate_230_part_23_E

noncomputable def certificate_230_part_26_E : List (ℕ × ℕ) := certificate_230_part_25_E

noncomputable def certificate_230_part_30_E : List (ℕ × ℕ) := certificate_230_part_26_E

noncomputable def certificate_231_q : Finset ℕ := ([0,1,2,5,8] : List ℕ).toFinset
noncomputable def certificate_231_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,2),(0,5),(0,8),(1,2),(1,5),(1,8),(2,5),(2,8),(5,8)]

noncomputable def certificate_232_q : Finset ℕ := ([0,1,2,5,9] : List ℕ).toFinset
noncomputable def certificate_232_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,5),(0,9),(1,2),(1,5),(1,9),(2,5),(2,9),(5,9)]

noncomputable def certificate_233_q : Finset ℕ := ([0,1,2,5,10] : List ℕ).toFinset
noncomputable def certificate_233_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,5),(0,10),(1,2),(1,5),(1,10),(2,5),(2,10),(5,10)]

noncomputable def certificate_234_q : Finset ℕ := ([0,1,2,6,10] : List ℕ).toFinset

noncomputable def certificate_234_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,6),(0,10),(1,2),(1,6),(1,10),(2,6),(2,10),(6,10)]

noncomputable def certificate_234_E : List (ℕ × ℕ) := certificate_234_edges

noncomputable def certificate_234_part_1_E : List (ℕ × ℕ) := certificate_234_E

noncomputable def certificate_234_part_2_E : List (ℕ × ℕ) := certificate_234_part_1_E

noncomputable def certificate_234_part_3_E : List (ℕ × ℕ) := certificate_234_part_2_E

noncomputable def certificate_234_part_4_E : List (ℕ × ℕ) := certificate_234_part_3_E

noncomputable def certificate_234_part_6_E : List (ℕ × ℕ) := certificate_234_part_4_E

noncomputable def certificate_234_part_7_E : List (ℕ × ℕ) := certificate_234_part_6_E

noncomputable def certificate_234_part_8_E : List (ℕ × ℕ) := certificate_234_part_7_E

noncomputable def certificate_234_part_9_E : List (ℕ × ℕ) := certificate_234_part_8_E

noncomputable def certificate_234_part_10_E : List (ℕ × ℕ) := certificate_234_part_9_E

noncomputable def certificate_234_part_12_E : List (ℕ × ℕ) := certificate_234_part_10_E

noncomputable def certificate_234_part_13_E : List (ℕ × ℕ) := certificate_234_part_12_E

noncomputable def certificate_234_part_14_E : List (ℕ × ℕ) := certificate_234_part_13_E

noncomputable def certificate_234_part_15_E : List (ℕ × ℕ) := certificate_234_part_14_E

noncomputable def certificate_234_part_19_E : List (ℕ × ℕ) := certificate_234_part_15_E

noncomputable def certificate_234_part_21_E : List (ℕ × ℕ) := certificate_234_part_19_E

noncomputable def certificate_234_part_27_E : List (ℕ × ℕ) := certificate_234_part_21_E

noncomputable def certificate_235_q : Finset ℕ := ([0,1,3,4,6] : List ℕ).toFinset
noncomputable def certificate_235_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(0,1),(0,3),(0,4),(0,6),(1,3),(1,4),(1,6),(3,4),(3,6),(4,6)]

noncomputable def certificate_236_q : Finset ℕ := ([0,1,3,4,7] : List ℕ).toFinset
noncomputable def certificate_236_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(0,1),(0,3),(0,4),(0,7),(1,3),(1,4),(1,7),(3,4),(3,7),(4,7)]

noncomputable def certificate_237_q : Finset ℕ := ([0,1,3,4,8] : List ℕ).toFinset
noncomputable def certificate_237_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,4),(0,8),(1,3),(1,4),(1,8),(3,4),(3,8),(4,8)]

noncomputable def certificate_238_q : Finset ℕ := ([0,1,3,4,9] : List ℕ).toFinset
noncomputable def certificate_238_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,4),(0,9),(1,3),(1,4),(1,9),(3,4),(3,9),(4,9)]

noncomputable def certificate_239_q : Finset ℕ := ([0,1,3,4,10] : List ℕ).toFinset

noncomputable def certificate_239_edges : List (ℕ × ℕ) := [(1,2),(2,3),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,4),(0,10),(1,3),(1,4),(1,10),(3,4),(3,10),(4,10)]

noncomputable def certificate_239_E : List (ℕ × ℕ) := certificate_239_edges

noncomputable def certificate_239_part_1_E : List (ℕ × ℕ) := certificate_239_E

noncomputable def certificate_239_part_2_E : List (ℕ × ℕ) := certificate_239_part_1_E

noncomputable def certificate_239_part_3_E : List (ℕ × ℕ) := certificate_239_part_2_E

noncomputable def certificate_239_part_4_E : List (ℕ × ℕ) := certificate_239_part_3_E

noncomputable def certificate_239_part_5_E : List (ℕ × ℕ) := certificate_239_part_4_E

noncomputable def certificate_239_part_7_E : List (ℕ × ℕ) := certificate_239_part_5_E

noncomputable def certificate_239_part_8_E : List (ℕ × ℕ) := certificate_239_part_7_E

noncomputable def certificate_239_part_11_E : List (ℕ × ℕ) := certificate_239_part_8_E

noncomputable def certificate_239_part_16_E : List (ℕ × ℕ) := certificate_239_part_11_E

noncomputable def certificate_239_part_19_E : List (ℕ × ℕ) := certificate_239_part_16_E

noncomputable def certificate_239_part_20_E : List (ℕ × ℕ) := certificate_239_part_19_E

noncomputable def certificate_239_part_28_E : List (ℕ × ℕ) := certificate_239_part_20_E

noncomputable def certificate_240_q : Finset ℕ := ([0,1,3,5,7] : List ℕ).toFinset
noncomputable def certificate_240_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,1),(0,3),(0,5),(0,7),(1,3),(1,5),(1,7),(3,5),(3,7),(5,7)]

noncomputable def certificate_241_q : Finset ℕ := ([0,1,3,5,8] : List ℕ).toFinset
noncomputable def certificate_241_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,5),(0,8),(1,3),(1,5),(1,8),(3,5),(3,8),(5,8)]

noncomputable def certificate_242_q : Finset ℕ := ([0,1,3,5,9] : List ℕ).toFinset
noncomputable def certificate_242_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,5),(0,9),(1,3),(1,5),(1,9),(3,5),(3,9),(5,9)]

noncomputable def certificate_243_q : Finset ℕ := ([0,1,3,5,10] : List ℕ).toFinset
noncomputable def certificate_243_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,5),(0,10),(1,3),(1,5),(1,10),(3,5),(3,10),(5,10)]

noncomputable def certificate_244_q : Finset ℕ := ([0,1,3,6,8] : List ℕ).toFinset
noncomputable def certificate_244_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,1),(0,3),(0,6),(0,8),(1,3),(1,6),(1,8),(3,6),(3,8),(6,8)]

noncomputable def certificate_245_q : Finset ℕ := ([0,1,3,6,9] : List ℕ).toFinset
noncomputable def certificate_245_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,6),(0,9),(1,3),(1,6),(1,9),(3,6),(3,9),(6,9)]

noncomputable def certificate_246_q : Finset ℕ := ([0,1,3,6,10] : List ℕ).toFinset
noncomputable def certificate_246_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,6),(0,10),(1,3),(1,6),(1,10),(3,6),(3,10),(6,10)]

noncomputable def certificate_247_q : Finset ℕ := ([0,1,3,7,9] : List ℕ).toFinset
noncomputable def certificate_247_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,3),(0,7),(0,9),(1,3),(1,7),(1,9),(3,7),(3,9),(7,9)]

noncomputable def certificate_248_q : Finset ℕ := ([0,1,3,7,10] : List ℕ).toFinset
noncomputable def certificate_248_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,7),(0,10),(1,3),(1,7),(1,10),(3,7),(3,10),(7,10)]

noncomputable def certificate_249_q : Finset ℕ := ([0,1,3,8,10] : List ℕ).toFinset
noncomputable def certificate_249_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,3),(0,8),(0,10),(1,3),(1,8),(1,10),(3,8),(3,10),(8,10)]

noncomputable def certificate_250_q : Finset ℕ := ([0,1,4,5,8] : List ℕ).toFinset
noncomputable def certificate_250_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(0,1),(0,4),(0,5),(0,8),(1,4),(1,5),(1,8),(4,5),(4,8),(5,8)]

noncomputable def certificate_251_q : Finset ℕ := ([0,1,4,5,9] : List ℕ).toFinset
noncomputable def certificate_251_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(0,1),(0,4),(0,5),(0,9),(1,4),(1,5),(1,9),(4,5),(4,9),(5,9)]

noncomputable def certificate_252_q : Finset ℕ := ([0,1,4,5,10] : List ℕ).toFinset

noncomputable def certificate_252_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,4),(0,5),(0,10),(1,4),(1,5),(1,10),(4,5),(4,10),(5,10)]

noncomputable def certificate_252_E : List (ℕ × ℕ) := certificate_252_edges

noncomputable def certificate_252_part_1_E : List (ℕ × ℕ) := certificate_252_E

noncomputable def certificate_252_part_2_E : List (ℕ × ℕ) := certificate_252_part_1_E

noncomputable def certificate_252_part_3_E : List (ℕ × ℕ) := certificate_252_part_2_E

noncomputable def certificate_252_part_4_E : List (ℕ × ℕ) := certificate_252_part_3_E

noncomputable def certificate_252_part_5_E : List (ℕ × ℕ) := certificate_252_part_4_E

noncomputable def certificate_252_part_6_E : List (ℕ × ℕ) := certificate_252_part_5_E

noncomputable def certificate_252_part_7_E : List (ℕ × ℕ) := certificate_252_part_6_E

noncomputable def certificate_252_part_8_E : List (ℕ × ℕ) := certificate_252_part_7_E

noncomputable def certificate_252_part_9_E : List (ℕ × ℕ) := certificate_252_part_8_E

noncomputable def certificate_252_part_11_E : List (ℕ × ℕ) := certificate_252_part_9_E

noncomputable def certificate_252_part_14_E : List (ℕ × ℕ) := certificate_252_part_11_E

noncomputable def certificate_252_part_15_E : List (ℕ × ℕ) := certificate_252_part_14_E

noncomputable def certificate_252_part_16_E : List (ℕ × ℕ) := certificate_252_part_15_E

noncomputable def certificate_252_part_19_E : List (ℕ × ℕ) := certificate_252_part_16_E

noncomputable def certificate_252_part_22_E : List (ℕ × ℕ) := certificate_252_part_19_E

noncomputable def certificate_252_part_23_E : List (ℕ × ℕ) := certificate_252_part_22_E

noncomputable def certificate_253_q : Finset ℕ := ([0,1,4,6,9] : List ℕ).toFinset
noncomputable def certificate_253_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,1),(0,4),(0,6),(0,9),(1,4),(1,6),(1,9),(4,6),(4,9),(6,9)]

noncomputable def certificate_254_q : Finset ℕ := ([0,1,4,6,10] : List ℕ).toFinset
noncomputable def certificate_254_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,4),(0,6),(0,10),(1,4),(1,6),(1,10),(4,6),(4,10),(6,10)]

noncomputable def certificate_255_q : Finset ℕ := ([0,1,4,7,10] : List ℕ).toFinset
noncomputable def certificate_255_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,4),(0,7),(0,10),(1,4),(1,7),(1,10),(4,7),(4,10),(7,10)]

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

noncomputable def certificate_256_q : Finset ℕ := ([0,1,5,6,10] : List ℕ).toFinset

noncomputable def certificate_256_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,5),(0,6),(0,10),(1,5),(1,6),(1,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_256_E : List (ℕ × ℕ) := certificate_256_edges

noncomputable def certificate_256_part_1_E : List (ℕ × ℕ) := certificate_256_E

noncomputable def certificate_256_part_2_E : List (ℕ × ℕ) := certificate_256_part_1_E

noncomputable def certificate_256_part_3_E : List (ℕ × ℕ) := certificate_256_part_2_E

noncomputable def certificate_256_part_4_E : List (ℕ × ℕ) := certificate_256_part_3_E

noncomputable def certificate_256_part_6_E : List (ℕ × ℕ) := certificate_256_part_4_E

noncomputable def certificate_256_part_7_E : List (ℕ × ℕ) := certificate_256_part_6_E

noncomputable def certificate_256_part_8_E : List (ℕ × ℕ) := certificate_256_part_7_E

noncomputable def certificate_256_part_9_E : List (ℕ × ℕ) := certificate_256_part_8_E

noncomputable def certificate_256_part_10_E : List (ℕ × ℕ) := certificate_256_part_9_E

noncomputable def certificate_256_part_13_E : List (ℕ × ℕ) := certificate_256_part_10_E

noncomputable def certificate_256_part_14_E : List (ℕ × ℕ) := certificate_256_part_13_E

noncomputable def certificate_256_part_16_E : List (ℕ × ℕ) := certificate_256_part_14_E

noncomputable def certificate_256_part_17_E : List (ℕ × ℕ) := certificate_256_part_16_E

noncomputable def certificate_256_part_18_E : List (ℕ × ℕ) := certificate_256_part_17_E

noncomputable def certificate_256_part_19_E : List (ℕ × ℕ) := certificate_256_part_18_E

noncomputable def certificate_256_part_20_E : List (ℕ × ℕ) := certificate_256_part_19_E

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

noncomputable def certificate_2066_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,9),(0,12),(0,15),(1,3),(1,5),(1,6),(1,9),(1,12),(1,15),(3,5),(3,6),(3,9),(3,12),(3,15),(5,6),(5,9),(5,12),(5,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2067_q : Finset ℕ := ([0,1,3,5,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2067_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,6),(0,10),(0,11),(0,15),(1,3),(1,5),(1,6),(1,10),(1,11),(1,15),(3,5),(3,6),(3,10),(3,11),(3,15),(5,6),(5,10),(5,11),(5,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2068_q : Finset ℕ := ([0,1,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2068_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(1,3),(1,5),(1,7),(1,8),(1,10),(1,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2069_q : Finset ℕ := ([0,1,3,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2069_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,14),(1,3),(1,5),(1,7),(1,8),(1,10),(1,14),(3,5),(3,7),(3,8),(3,10),(3,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2070_q : Finset ℕ := ([0,1,3,5,7,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2070_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,8),(0,10),(0,15),(1,3),(1,5),(1,7),(1,8),(1,10),(1,15),(3,5),(3,7),(3,8),(3,10),(3,15),(5,7),(5,8),(5,10),(5,15),(7,8),(7,10),(7,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2071_q : Finset ℕ := ([0,1,3,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2071_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(0,14),(1,3),(1,5),(1,7),(1,8),(1,11),(1,14),(3,5),(3,7),(3,8),(3,11),(3,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2072_q : Finset ℕ := ([0,1,3,5,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2072_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,8),(0,11),(0,15),(1,3),(1,5),(1,7),(1,8),(1,11),(1,15),(3,5),(3,7),(3,8),(3,11),(3,15),(5,7),(5,8),(5,11),(5,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2073_q : Finset ℕ := ([0,1,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2073_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(1,3),(1,5),(1,7),(1,9),(1,10),(1,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2074_q : Finset ℕ := ([0,1,3,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2074_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,14),(1,3),(1,5),(1,7),(1,9),(1,10),(1,14),(3,5),(3,7),(3,9),(3,10),(3,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2075_q : Finset ℕ := ([0,1,3,5,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2075_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,10),(0,15),(1,3),(1,5),(1,7),(1,9),(1,10),(1,15),(3,5),(3,7),(3,9),(3,10),(3,15),(5,7),(5,9),(5,10),(5,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2076_q : Finset ℕ := ([0,1,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2076_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(1,3),(1,5),(1,7),(1,9),(1,11),(1,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2077_q : Finset ℕ := ([0,1,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2077_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(1,3),(1,5),(1,7),(1,9),(1,11),(1,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2078_q : Finset ℕ := ([0,1,3,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2078_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,11),(0,15),(1,3),(1,5),(1,7),(1,9),(1,11),(1,15),(3,5),(3,7),(3,9),(3,11),(3,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2079_q : Finset ℕ := ([0,1,3,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2079_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(0,14),(1,3),(1,5),(1,7),(1,9),(1,12),(1,14),(3,5),(3,7),(3,9),(3,12),(3,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates066
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2080_q : Finset ℕ := ([0,1,3,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2080_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,12),(0,15),(1,3),(1,5),(1,7),(1,9),(1,12),(1,15),(3,5),(3,7),(3,9),(3,12),(3,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2081_q : Finset ℕ := ([0,1,3,5,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2081_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,9),(0,13),(0,15),(1,3),(1,5),(1,7),(1,9),(1,13),(1,15),(3,5),(3,7),(3,9),(3,13),(3,15),(5,7),(5,9),(5,13),(5,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2082_q : Finset ℕ := ([0,1,3,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2082_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,11),(0,14),(1,3),(1,5),(1,7),(1,10),(1,11),(1,14),(3,5),(3,7),(3,10),(3,11),(3,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2083_q : Finset ℕ := ([0,1,3,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2083_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,10),(0,11),(0,15),(1,3),(1,5),(1,7),(1,10),(1,11),(1,15),(3,5),(3,7),(3,10),(3,11),(3,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2084_q : Finset ℕ := ([0,1,3,5,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_2084_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(0,14),(1,3),(1,5),(1,7),(1,10),(1,12),(1,14),(3,5),(3,7),(3,10),(3,12),(3,14),(5,7),(5,10),(5,12),(5,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_2085_q : Finset ℕ := ([0,1,3,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2085_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,10),(0,12),(0,15),(1,3),(1,5),(1,7),(1,10),(1,12),(1,15),(3,5),(3,7),(3,10),(3,12),(3,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2086_q : Finset ℕ := ([0,1,3,5,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2086_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,10),(0,13),(0,15),(1,3),(1,5),(1,7),(1,10),(1,13),(1,15),(3,5),(3,7),(3,10),(3,13),(3,15),(5,7),(5,10),(5,13),(5,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2087_q : Finset ℕ := ([0,1,3,5,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2087_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,11),(0,12),(0,15),(1,3),(1,5),(1,7),(1,11),(1,12),(1,15),(3,5),(3,7),(3,11),(3,12),(3,15),(5,7),(5,11),(5,12),(5,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2088_q : Finset ℕ := ([0,1,3,5,7,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2088_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,7),(0,11),(0,13),(0,15),(1,3),(1,5),(1,7),(1,11),(1,13),(1,15),(3,5),(3,7),(3,11),(3,13),(3,15),(5,7),(5,11),(5,13),(5,15),(7,11),(7,13),(7,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2089_q : Finset ℕ := ([0,1,3,5,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2089_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,9),(0,11),(0,14),(1,3),(1,5),(1,8),(1,9),(1,11),(1,14),(3,5),(3,8),(3,9),(3,11),(3,14),(5,8),(5,9),(5,11),(5,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2090_q : Finset ℕ := ([0,1,3,5,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2090_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,9),(0,11),(0,15),(1,3),(1,5),(1,8),(1,9),(1,11),(1,15),(3,5),(3,8),(3,9),(3,11),(3,15),(5,8),(5,9),(5,11),(5,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2091_q : Finset ℕ := ([0,1,3,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2091_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,9),(0,12),(0,15),(1,3),(1,5),(1,8),(1,9),(1,12),(1,15),(3,5),(3,8),(3,9),(3,12),(3,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2092_q : Finset ℕ := ([0,1,3,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2092_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,5),(0,8),(0,10),(0,11),(0,14),(1,3),(1,5),(1,8),(1,10),(1,11),(1,14),(3,5),(3,8),(3,10),(3,11),(3,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2093_q : Finset ℕ := ([0,1,3,5,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2093_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,10),(0,11),(0,15),(1,3),(1,5),(1,8),(1,10),(1,11),(1,15),(3,5),(3,8),(3,10),(3,11),(3,15),(5,8),(5,10),(5,11),(5,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2094_q : Finset ℕ := ([0,1,3,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2094_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,10),(0,12),(0,15),(1,3),(1,5),(1,8),(1,10),(1,12),(1,15),(3,5),(3,8),(3,10),(3,12),(3,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2095_q : Finset ℕ := ([0,1,3,5,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2095_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,10),(0,13),(0,15),(1,3),(1,5),(1,8),(1,10),(1,13),(1,15),(3,5),(3,8),(3,10),(3,13),(3,15),(5,8),(5,10),(5,13),(5,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2096_q : Finset ℕ := ([0,1,3,5,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2096_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,11),(0,12),(0,15),(1,3),(1,5),(1,8),(1,11),(1,12),(1,15),(3,5),(3,8),(3,11),(3,12),(3,15),(5,8),(5,11),(5,12),(5,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2097_q : Finset ℕ := ([0,1,3,5,8,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2097_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,8),(0,11),(0,13),(0,15),(1,3),(1,5),(1,8),(1,11),(1,13),(1,15),(3,5),(3,8),(3,11),(3,13),(3,15),(5,8),(5,11),(5,13),(5,15),(8,11),(8,13),(8,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2098_q : Finset ℕ := ([0,1,3,5,9,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2098_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,9),(0,10),(0,12),(0,15),(1,3),(1,5),(1,9),(1,10),(1,12),(1,15),(3,5),(3,9),(3,10),(3,12),(3,15),(5,9),(5,10),(5,12),(5,15),(9,10),(9,12),(9,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2099_q : Finset ℕ := ([0,1,3,5,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2099_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,5),(0,9),(0,11),(0,12),(0,15),(1,3),(1,5),(1,9),(1,11),(1,12),(1,15),(3,5),(3,9),(3,11),(3,12),(3,15),(5,9),(5,11),(5,12),(5,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2100_q : Finset ℕ := ([0,1,3,6,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2100_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(0,14),(1,3),(1,6),(1,7),(1,9),(1,12),(1,14),(3,6),(3,7),(3,9),(3,12),(3,14),(6,7),(6,9),(6,12),(6,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2101_q : Finset ℕ := ([0,1,3,6,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2101_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,9),(0,12),(0,15),(1,3),(1,6),(1,7),(1,9),(1,12),(1,15),(3,6),(3,7),(3,9),(3,12),(3,15),(6,7),(6,9),(6,12),(6,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2102_q : Finset ℕ := ([0,1,3,6,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2102_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,9),(0,13),(0,15),(1,3),(1,6),(1,7),(1,9),(1,13),(1,15),(3,6),(3,7),(3,9),(3,13),(3,15),(6,7),(6,9),(6,13),(6,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2103_q : Finset ℕ := ([0,1,3,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2103_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,3),(0,6),(0,7),(0,10),(0,11),(0,14),(1,3),(1,6),(1,7),(1,10),(1,11),(1,14),(3,6),(3,7),(3,10),(3,11),(3,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2104_q : Finset ℕ := ([0,1,3,6,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2104_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,10),(0,11),(0,15),(1,3),(1,6),(1,7),(1,10),(1,11),(1,15),(3,6),(3,7),(3,10),(3,11),(3,15),(6,7),(6,10),(6,11),(6,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2105_q : Finset ℕ := ([0,1,3,6,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2105_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,7),(0,10),(0,12),(0,15),(1,3),(1,6),(1,7),(1,10),(1,12),(1,15),(3,6),(3,7),(3,10),(3,12),(3,15),(6,7),(6,10),(6,12),(6,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2106_q : Finset ℕ := ([0,1,3,6,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2106_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,9),(0,11),(0,15),(1,3),(1,6),(1,8),(1,9),(1,11),(1,15),(3,6),(3,8),(3,9),(3,11),(3,15),(6,8),(6,9),(6,11),(6,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2107_q : Finset ℕ := ([0,1,3,6,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2107_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,9),(0,12),(0,15),(1,3),(1,6),(1,8),(1,9),(1,12),(1,15),(3,6),(3,8),(3,9),(3,12),(3,15),(6,8),(6,9),(6,12),(6,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2108_q : Finset ℕ := ([0,1,3,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2108_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,10),(0,12),(0,15),(1,3),(1,6),(1,8),(1,10),(1,12),(1,15),(3,6),(3,8),(3,10),(3,12),(3,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2109_q : Finset ℕ := ([0,1,3,6,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2109_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,10),(0,13),(0,15),(1,3),(1,6),(1,8),(1,10),(1,13),(1,15),(3,6),(3,8),(3,10),(3,13),(3,15),(6,8),(6,10),(6,13),(6,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2110_q : Finset ℕ := ([0,1,3,6,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2110_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,8),(0,11),(0,12),(0,15),(1,3),(1,6),(1,8),(1,11),(1,12),(1,15),(3,6),(3,8),(3,11),(3,12),(3,15),(6,8),(6,11),(6,12),(6,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2111_q : Finset ℕ := ([0,1,3,6,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2111_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,6),(0,9),(0,11),(0,12),(0,15),(1,3),(1,6),(1,9),(1,11),(1,12),(1,15),(3,6),(3,9),(3,11),(3,12),(3,15),(6,9),(6,11),(6,12),(6,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates067
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2112_q : Finset ℕ := ([0,1,3,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2112_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,3),(0,7),(0,8),(0,11),(0,12),(0,15),(1,3),(1,7),(1,8),(1,11),(1,12),(1,15),(3,7),(3,8),(3,11),(3,12),(3,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2113_q : Finset ℕ := ([0,1,4,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2113_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,4),(0,5),(0,8),(0,9),(0,12),(0,15),(1,4),(1,5),(1,8),(1,9),(1,12),(1,15),(4,5),(4,8),(4,9),(4,12),(4,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2114_q : Finset ℕ := ([0,1,4,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2114_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,4),(0,5),(0,8),(0,10),(0,12),(0,15),(1,4),(1,5),(1,8),(1,10),(1,12),(1,15),(4,5),(4,8),(4,10),(4,12),(4,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2115_q : Finset ℕ := ([0,1,4,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2115_edges : List (ℕ × ℕ) := [(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,4),(0,6),(0,8),(0,10),(0,12),(0,15),(1,4),(1,6),(1,8),(1,10),(1,12),(1,15),(4,6),(4,8),(4,10),(4,12),(4,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2116_q : Finset ℕ := ([0,2,3,5,6,8,9,11] : List ℕ).toFinset
noncomputable def certificate_2116_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,11),(2,3),(2,5),(2,6),(2,8),(2,9),(2,11),(3,5),(3,6),(3,8),(3,9),(3,11),(5,6),(5,8),(5,9),(5,11),(6,8),(6,9),(6,11),(8,9),(8,11),(9,11)]

noncomputable def certificate_2117_q : Finset ℕ := ([0,2,3,5,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2117_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,12),(2,3),(2,5),(2,6),(2,8),(2,9),(2,12),(3,5),(3,6),(3,8),(3,9),(3,12),(5,6),(5,8),(5,9),(5,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2118_q : Finset ℕ := ([0,2,3,5,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2118_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,13),(2,3),(2,5),(2,6),(2,8),(2,9),(2,13),(3,5),(3,6),(3,8),(3,9),(3,13),(5,6),(5,8),(5,9),(5,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2119_q : Finset ℕ := ([0,2,3,5,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2119_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,14),(2,3),(2,5),(2,6),(2,8),(2,9),(2,14),(3,5),(3,6),(3,8),(3,9),(3,14),(5,6),(5,8),(5,9),(5,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2120_q : Finset ℕ := ([0,2,3,5,6,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2120_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,9),(0,15),(2,3),(2,5),(2,6),(2,8),(2,9),(2,15),(3,5),(3,6),(3,8),(3,9),(3,15),(5,6),(5,8),(5,9),(5,15),(6,8),(6,9),(6,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2121_q : Finset ℕ := ([0,2,3,5,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2121_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,12),(2,3),(2,5),(2,6),(2,8),(2,10),(2,12),(3,5),(3,6),(3,8),(3,10),(3,12),(5,6),(5,8),(5,10),(5,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2122_q : Finset ℕ := ([0,2,3,5,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2122_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,13),(2,3),(2,5),(2,6),(2,8),(2,10),(2,13),(3,5),(3,6),(3,8),(3,10),(3,13),(5,6),(5,8),(5,10),(5,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2123_q : Finset ℕ := ([0,2,3,5,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2123_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,14),(2,3),(2,5),(2,6),(2,8),(2,10),(2,14),(3,5),(3,6),(3,8),(3,10),(3,14),(5,6),(5,8),(5,10),(5,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2124_q : Finset ℕ := ([0,2,3,5,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2124_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(0,15),(2,3),(2,5),(2,6),(2,8),(2,10),(2,15),(3,5),(3,6),(3,8),(3,10),(3,15),(5,6),(5,8),(5,10),(5,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2125_q : Finset ℕ := ([0,2,3,5,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2125_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,13),(2,3),(2,5),(2,6),(2,8),(2,11),(2,13),(3,5),(3,6),(3,8),(3,11),(3,13),(5,6),(5,8),(5,11),(5,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2126_q : Finset ℕ := ([0,2,3,5,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2126_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,14),(2,3),(2,5),(2,6),(2,8),(2,11),(2,14),(3,5),(3,6),(3,8),(3,11),(3,14),(5,6),(5,8),(5,11),(5,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2127_q : Finset ℕ := ([0,2,3,5,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2127_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(0,15),(2,3),(2,5),(2,6),(2,8),(2,11),(2,15),(3,5),(3,6),(3,8),(3,11),(3,15),(5,6),(5,8),(5,11),(5,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2128_q : Finset ℕ := ([0,2,3,5,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2128_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(0,14),(2,3),(2,5),(2,6),(2,8),(2,12),(2,14),(3,5),(3,6),(3,8),(3,12),(3,14),(5,6),(5,8),(5,12),(5,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2129_q : Finset ℕ := ([0,2,3,5,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2129_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(0,15),(2,3),(2,5),(2,6),(2,8),(2,12),(2,15),(3,5),(3,6),(3,8),(3,12),(3,15),(5,6),(5,8),(5,12),(5,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2130_q : Finset ℕ := ([0,2,3,5,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2130_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(0,15),(2,3),(2,5),(2,6),(2,8),(2,13),(2,15),(3,5),(3,6),(3,8),(3,13),(3,15),(5,6),(5,8),(5,13),(5,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2131_q : Finset ℕ := ([0,2,3,5,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2131_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,13),(2,3),(2,5),(2,6),(2,9),(2,10),(2,13),(3,5),(3,6),(3,9),(3,10),(3,13),(5,6),(5,9),(5,10),(5,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2132_q : Finset ℕ := ([0,2,3,5,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2132_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,14),(2,3),(2,5),(2,6),(2,9),(2,10),(2,14),(3,5),(3,6),(3,9),(3,10),(3,14),(5,6),(5,9),(5,10),(5,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2133_q : Finset ℕ := ([0,2,3,5,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2133_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,9),(0,10),(0,15),(2,3),(2,5),(2,6),(2,9),(2,10),(2,15),(3,5),(3,6),(3,9),(3,10),(3,15),(5,6),(5,9),(5,10),(5,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2134_q : Finset ℕ := ([0,2,3,5,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2134_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,6),(0,9),(0,11),(0,14),(2,3),(2,5),(2,6),(2,9),(2,11),(2,14),(3,5),(3,6),(3,9),(3,11),(3,14),(5,6),(5,9),(5,11),(5,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2135_q : Finset ℕ := ([0,2,3,5,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2135_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,9),(0,11),(0,15),(2,3),(2,5),(2,6),(2,9),(2,11),(2,15),(3,5),(3,6),(3,9),(3,11),(3,15),(5,6),(5,9),(5,11),(5,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2136_q : Finset ℕ := ([0,2,3,5,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2136_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(0,15),(2,3),(2,5),(2,6),(2,9),(2,12),(2,15),(3,5),(3,6),(3,9),(3,12),(3,15),(5,6),(5,9),(5,12),(5,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2137_q : Finset ℕ := ([0,2,3,5,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2137_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,6),(0,10),(0,11),(0,15),(2,3),(2,5),(2,6),(2,10),(2,11),(2,15),(3,5),(3,6),(3,10),(3,11),(3,15),(5,6),(5,10),(5,11),(5,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2138_q : Finset ℕ := ([0,2,3,5,7,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2138_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,12),(2,3),(2,5),(2,7),(2,8),(2,10),(2,12),(3,5),(3,7),(3,8),(3,10),(3,12),(5,7),(5,8),(5,10),(5,12),(7,8),(7,10),(7,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2139_q : Finset ℕ := ([0,2,3,5,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2139_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,13),(2,3),(2,5),(2,7),(2,8),(2,10),(2,13),(3,5),(3,7),(3,8),(3,10),(3,13),(5,7),(5,8),(5,10),(5,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2140_q : Finset ℕ := ([0,2,3,5,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2140_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,14),(2,3),(2,5),(2,7),(2,8),(2,10),(2,14),(3,5),(3,7),(3,8),(3,10),(3,14),(5,7),(5,8),(5,10),(5,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2141_q : Finset ℕ := ([0,2,3,5,7,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2141_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,8),(0,10),(0,15),(2,3),(2,5),(2,7),(2,8),(2,10),(2,15),(3,5),(3,7),(3,8),(3,10),(3,15),(5,7),(5,8),(5,10),(5,15),(7,8),(7,10),(7,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2142_q : Finset ℕ := ([0,2,3,5,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2142_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(0,14),(2,3),(2,5),(2,7),(2,8),(2,11),(2,14),(3,5),(3,7),(3,8),(3,11),(3,14),(5,7),(5,8),(5,11),(5,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2143_q : Finset ℕ := ([0,2,3,5,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2143_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(0,15),(2,3),(2,5),(2,7),(2,8),(2,11),(2,15),(3,5),(3,7),(3,8),(3,11),(3,15),(5,7),(5,8),(5,11),(5,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates068
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2144_q : Finset ℕ := ([0,2,3,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2144_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,13),(2,3),(2,5),(2,7),(2,9),(2,10),(2,13),(3,5),(3,7),(3,9),(3,10),(3,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2145_q : Finset ℕ := ([0,2,3,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2145_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,14),(2,3),(2,5),(2,7),(2,9),(2,10),(2,14),(3,5),(3,7),(3,9),(3,10),(3,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2146_q : Finset ℕ := ([0,2,3,5,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2146_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,10),(0,15),(2,3),(2,5),(2,7),(2,9),(2,10),(2,15),(3,5),(3,7),(3,9),(3,10),(3,15),(5,7),(5,9),(5,10),(5,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2147_q : Finset ℕ := ([0,2,3,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2147_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,13),(2,3),(2,5),(2,7),(2,9),(2,11),(2,13),(3,5),(3,7),(3,9),(3,11),(3,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2148_q : Finset ℕ := ([0,2,3,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2148_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,14),(2,3),(2,5),(2,7),(2,9),(2,11),(2,14),(3,5),(3,7),(3,9),(3,11),(3,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2149_q : Finset ℕ := ([0,2,3,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2149_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(0,15),(2,3),(2,5),(2,7),(2,9),(2,11),(2,15),(3,5),(3,7),(3,9),(3,11),(3,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2150_q : Finset ℕ := ([0,2,3,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2150_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(0,14),(2,3),(2,5),(2,7),(2,9),(2,12),(2,14),(3,5),(3,7),(3,9),(3,12),(3,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2151_q : Finset ℕ := ([0,2,3,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2151_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(0,15),(2,3),(2,5),(2,7),(2,9),(2,12),(2,15),(3,5),(3,7),(3,9),(3,12),(3,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2152_q : Finset ℕ := ([0,2,3,5,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2152_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(0,15),(2,3),(2,5),(2,7),(2,9),(2,13),(2,15),(3,5),(3,7),(3,9),(3,13),(3,15),(5,7),(5,9),(5,13),(5,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2153_q : Finset ℕ := ([0,2,3,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2153_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,11),(0,14),(2,3),(2,5),(2,7),(2,10),(2,11),(2,14),(3,5),(3,7),(3,10),(3,11),(3,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2154_q : Finset ℕ := ([0,2,3,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2154_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,10),(0,11),(0,15),(2,3),(2,5),(2,7),(2,10),(2,11),(2,15),(3,5),(3,7),(3,10),(3,11),(3,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2155_q : Finset ℕ := ([0,2,3,5,7,10,12,14] : List ℕ).toFinset
noncomputable def certificate_2155_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(0,14),(2,3),(2,5),(2,7),(2,10),(2,12),(2,14),(3,5),(3,7),(3,10),(3,12),(3,14),(5,7),(5,10),(5,12),(5,14),(7,10),(7,12),(7,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_2156_q : Finset ℕ := ([0,2,3,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2156_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(0,15),(2,3),(2,5),(2,7),(2,10),(2,12),(2,15),(3,5),(3,7),(3,10),(3,12),(3,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2157_q : Finset ℕ := ([0,2,3,5,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2157_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(0,15),(2,3),(2,5),(2,7),(2,10),(2,13),(2,15),(3,5),(3,7),(3,10),(3,13),(3,15),(5,7),(5,10),(5,13),(5,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2158_q : Finset ℕ := ([0,2,3,5,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2158_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,11),(0,12),(0,15),(2,3),(2,5),(2,7),(2,11),(2,12),(2,15),(3,5),(3,7),(3,11),(3,12),(3,15),(5,7),(5,11),(5,12),(5,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2159_q : Finset ℕ := ([0,2,3,5,7,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2159_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(0,15),(2,3),(2,5),(2,7),(2,11),(2,13),(2,15),(3,5),(3,7),(3,11),(3,13),(3,15),(5,7),(5,11),(5,13),(5,15),(7,11),(7,13),(7,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2160_q : Finset ℕ := ([0,2,3,5,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2160_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,9),(0,11),(0,14),(2,3),(2,5),(2,8),(2,9),(2,11),(2,14),(3,5),(3,8),(3,9),(3,11),(3,14),(5,8),(5,9),(5,11),(5,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2161_q : Finset ℕ := ([0,2,3,5,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2161_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,9),(0,11),(0,15),(2,3),(2,5),(2,8),(2,9),(2,11),(2,15),(3,5),(3,8),(3,9),(3,11),(3,15),(5,8),(5,9),(5,11),(5,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2162_q : Finset ℕ := ([0,2,3,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2162_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(0,15),(2,3),(2,5),(2,8),(2,9),(2,12),(2,15),(3,5),(3,8),(3,9),(3,12),(3,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2163_q : Finset ℕ := ([0,2,3,5,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2163_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,5),(0,8),(0,10),(0,11),(0,14),(2,3),(2,5),(2,8),(2,10),(2,11),(2,14),(3,5),(3,8),(3,10),(3,11),(3,14),(5,8),(5,10),(5,11),(5,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2164_q : Finset ℕ := ([0,2,3,5,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2164_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,10),(0,11),(0,15),(2,3),(2,5),(2,8),(2,10),(2,11),(2,15),(3,5),(3,8),(3,10),(3,11),(3,15),(5,8),(5,10),(5,11),(5,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2165_q : Finset ℕ := ([0,2,3,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2165_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,10),(0,12),(0,15),(2,3),(2,5),(2,8),(2,10),(2,12),(2,15),(3,5),(3,8),(3,10),(3,12),(3,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2166_q : Finset ℕ := ([0,2,3,5,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2166_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(0,15),(2,3),(2,5),(2,8),(2,10),(2,13),(2,15),(3,5),(3,8),(3,10),(3,13),(3,15),(5,8),(5,10),(5,13),(5,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2167_q : Finset ℕ := ([0,2,3,5,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2167_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,8),(0,11),(0,12),(0,15),(2,3),(2,5),(2,8),(2,11),(2,12),(2,15),(3,5),(3,8),(3,11),(3,12),(3,15),(5,8),(5,11),(5,12),(5,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2168_q : Finset ℕ := ([0,2,3,5,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2168_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,3),(0,5),(0,9),(0,11),(0,12),(0,15),(2,3),(2,5),(2,9),(2,11),(2,12),(2,15),(3,5),(3,9),(3,11),(3,12),(3,15),(5,9),(5,11),(5,12),(5,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2169_q : Finset ℕ := ([0,2,3,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2169_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,3),(0,6),(0,7),(0,10),(0,11),(0,14),(2,3),(2,6),(2,7),(2,10),(2,11),(2,14),(3,6),(3,7),(3,10),(3,11),(3,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2170_q : Finset ℕ := ([0,2,3,6,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2170_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,6),(0,7),(0,10),(0,11),(0,15),(2,3),(2,6),(2,7),(2,10),(2,11),(2,15),(3,6),(3,7),(3,10),(3,11),(3,15),(6,7),(6,10),(6,11),(6,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2171_q : Finset ℕ := ([0,2,3,6,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2171_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,6),(0,7),(0,10),(0,12),(0,15),(2,3),(2,6),(2,7),(2,10),(2,12),(2,15),(3,6),(3,7),(3,10),(3,12),(3,15),(6,7),(6,10),(6,12),(6,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2172_q : Finset ℕ := ([0,2,3,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2172_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,3),(0,6),(0,8),(0,10),(0,12),(0,15),(2,3),(2,6),(2,8),(2,10),(2,12),(2,15),(3,6),(3,8),(3,10),(3,12),(3,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2173_q : Finset ℕ := ([0,2,4,5,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2173_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,13),(2,4),(2,5),(2,7),(2,9),(2,10),(2,13),(4,5),(4,7),(4,9),(4,10),(4,13),(5,7),(5,9),(5,10),(5,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2174_q : Finset ℕ := ([0,2,4,5,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2174_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,14),(2,4),(2,5),(2,7),(2,9),(2,10),(2,14),(4,5),(4,7),(4,9),(4,10),(4,14),(5,7),(5,9),(5,10),(5,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2175_q : Finset ℕ := ([0,2,4,5,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2175_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,10),(0,15),(2,4),(2,5),(2,7),(2,9),(2,10),(2,15),(4,5),(4,7),(4,9),(4,10),(4,15),(5,7),(5,9),(5,10),(5,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates069
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2176_q : Finset ℕ := ([0,2,4,5,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2176_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,13),(2,4),(2,5),(2,7),(2,9),(2,11),(2,13),(4,5),(4,7),(4,9),(4,11),(4,13),(5,7),(5,9),(5,11),(5,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2177_q : Finset ℕ := ([0,2,4,5,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2177_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,14),(2,4),(2,5),(2,7),(2,9),(2,11),(2,14),(4,5),(4,7),(4,9),(4,11),(4,14),(5,7),(5,9),(5,11),(5,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2178_q : Finset ℕ := ([0,2,4,5,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2178_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(0,15),(2,4),(2,5),(2,7),(2,9),(2,11),(2,15),(4,5),(4,7),(4,9),(4,11),(4,15),(5,7),(5,9),(5,11),(5,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2179_q : Finset ℕ := ([0,2,4,5,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2179_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(0,14),(2,4),(2,5),(2,7),(2,9),(2,12),(2,14),(4,5),(4,7),(4,9),(4,12),(4,14),(5,7),(5,9),(5,12),(5,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2180_q : Finset ℕ := ([0,2,4,5,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2180_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(0,15),(2,4),(2,5),(2,7),(2,9),(2,12),(2,15),(4,5),(4,7),(4,9),(4,12),(4,15),(5,7),(5,9),(5,12),(5,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2181_q : Finset ℕ := ([0,2,4,5,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2181_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(0,15),(2,4),(2,5),(2,7),(2,9),(2,13),(2,15),(4,5),(4,7),(4,9),(4,13),(4,15),(5,7),(5,9),(5,13),(5,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2182_q : Finset ℕ := ([0,2,4,5,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2182_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,5),(0,7),(0,10),(0,11),(0,14),(2,4),(2,5),(2,7),(2,10),(2,11),(2,14),(4,5),(4,7),(4,10),(4,11),(4,14),(5,7),(5,10),(5,11),(5,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2183_q : Finset ℕ := ([0,2,4,5,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2183_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,10),(0,11),(0,15),(2,4),(2,5),(2,7),(2,10),(2,11),(2,15),(4,5),(4,7),(4,10),(4,11),(4,15),(5,7),(5,10),(5,11),(5,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2184_q : Finset ℕ := ([0,2,4,5,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2184_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(0,15),(2,4),(2,5),(2,7),(2,10),(2,12),(2,15),(4,5),(4,7),(4,10),(4,12),(4,15),(5,7),(5,10),(5,12),(5,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2185_q : Finset ℕ := ([0,2,4,5,7,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2185_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(0,15),(2,4),(2,5),(2,7),(2,10),(2,13),(2,15),(4,5),(4,7),(4,10),(4,13),(4,15),(5,7),(5,10),(5,13),(5,15),(7,10),(7,13),(7,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2186_q : Finset ℕ := ([0,2,4,5,7,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2186_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,7),(0,11),(0,12),(0,15),(2,4),(2,5),(2,7),(2,11),(2,12),(2,15),(4,5),(4,7),(4,11),(4,12),(4,15),(5,7),(5,11),(5,12),(5,15),(7,11),(7,12),(7,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2187_q : Finset ℕ := ([0,2,4,5,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2187_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(0,15),(2,4),(2,5),(2,8),(2,9),(2,12),(2,15),(4,5),(4,8),(4,9),(4,12),(4,15),(5,8),(5,9),(5,12),(5,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2188_q : Finset ℕ := ([0,2,4,5,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2188_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,5),(0,8),(0,10),(0,12),(0,15),(2,4),(2,5),(2,8),(2,10),(2,12),(2,15),(4,5),(4,8),(4,10),(4,12),(4,15),(5,8),(5,10),(5,12),(5,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2189_q : Finset ℕ := ([0,2,4,6,7,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2189_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,13),(2,4),(2,6),(2,7),(2,9),(2,11),(2,13),(4,6),(4,7),(4,9),(4,11),(4,13),(6,7),(6,9),(6,11),(6,13),(7,9),(7,11),(7,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2190_q : Finset ℕ := ([0,2,4,6,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2190_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,14),(2,4),(2,6),(2,7),(2,9),(2,11),(2,14),(4,6),(4,7),(4,9),(4,11),(4,14),(6,7),(6,9),(6,11),(6,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2191_q : Finset ℕ := ([0,2,4,6,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2191_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(0,15),(2,4),(2,6),(2,7),(2,9),(2,11),(2,15),(4,6),(4,7),(4,9),(4,11),(4,15),(6,7),(6,9),(6,11),(6,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2192_q : Finset ℕ := ([0,2,4,6,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2192_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(0,14),(2,4),(2,6),(2,7),(2,9),(2,12),(2,14),(4,6),(4,7),(4,9),(4,12),(4,14),(6,7),(6,9),(6,12),(6,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2193_q : Finset ℕ := ([0,2,4,6,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2193_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(0,15),(2,4),(2,6),(2,7),(2,9),(2,12),(2,15),(4,6),(4,7),(4,9),(4,12),(4,15),(6,7),(6,9),(6,12),(6,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2194_q : Finset ℕ := ([0,2,4,6,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2194_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(0,15),(2,4),(2,6),(2,7),(2,9),(2,13),(2,15),(4,6),(4,7),(4,9),(4,13),(4,15),(6,7),(6,9),(6,13),(6,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2195_q : Finset ℕ := ([0,2,4,6,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2195_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,7),(0,10),(0,11),(0,14),(2,4),(2,6),(2,7),(2,10),(2,11),(2,14),(4,6),(4,7),(4,10),(4,11),(4,14),(6,7),(6,10),(6,11),(6,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2196_q : Finset ℕ := ([0,2,4,6,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2196_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,10),(0,11),(0,15),(2,4),(2,6),(2,7),(2,10),(2,11),(2,15),(4,6),(4,7),(4,10),(4,11),(4,15),(6,7),(6,10),(6,11),(6,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2197_q : Finset ℕ := ([0,2,4,6,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2197_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,7),(0,10),(0,12),(0,15),(2,4),(2,6),(2,7),(2,10),(2,12),(2,15),(4,6),(4,7),(4,10),(4,12),(4,15),(6,7),(6,10),(6,12),(6,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2198_q : Finset ℕ := ([0,2,4,6,8,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2198_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,9),(0,11),(0,14),(2,4),(2,6),(2,8),(2,9),(2,11),(2,14),(4,6),(4,8),(4,9),(4,11),(4,14),(6,8),(6,9),(6,11),(6,14),(8,9),(8,11),(8,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2199_q : Finset ℕ := ([0,2,4,6,8,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2199_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,9),(0,11),(0,15),(2,4),(2,6),(2,8),(2,9),(2,11),(2,15),(4,6),(4,8),(4,9),(4,11),(4,15),(6,8),(6,9),(6,11),(6,15),(8,9),(8,11),(8,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2200_q : Finset ℕ := ([0,2,4,6,8,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2200_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(0,15),(2,4),(2,6),(2,8),(2,9),(2,12),(2,15),(4,6),(4,8),(4,9),(4,12),(4,15),(6,8),(6,9),(6,12),(6,15),(8,9),(8,12),(8,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2201_q : Finset ℕ := ([0,2,4,6,8,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2201_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,11),(0,14),(2,4),(2,6),(2,8),(2,10),(2,11),(2,14),(4,6),(4,8),(4,10),(4,11),(4,14),(6,8),(6,10),(6,11),(6,14),(8,10),(8,11),(8,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2202_q : Finset ℕ := ([0,2,4,6,8,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2202_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,10),(0,11),(0,15),(2,4),(2,6),(2,8),(2,10),(2,11),(2,15),(4,6),(4,8),(4,10),(4,11),(4,15),(6,8),(6,10),(6,11),(6,15),(8,10),(8,11),(8,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2203_q : Finset ℕ := ([0,2,4,6,8,10,12,14] : List ℕ).toFinset
noncomputable def certificate_2203_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(0,14),(2,4),(2,6),(2,8),(2,10),(2,12),(2,14),(4,6),(4,8),(4,10),(4,12),(4,14),(6,8),(6,10),(6,12),(6,14),(8,10),(8,12),(8,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_2204_q : Finset ℕ := ([0,2,4,6,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2204_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(0,15),(2,4),(2,6),(2,8),(2,10),(2,12),(2,15),(4,6),(4,8),(4,10),(4,12),(4,15),(6,8),(6,10),(6,12),(6,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2205_q : Finset ℕ := ([0,2,4,6,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2205_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(0,15),(2,4),(2,6),(2,8),(2,10),(2,13),(2,15),(4,6),(4,8),(4,10),(4,13),(4,15),(6,8),(6,10),(6,13),(6,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2206_q : Finset ℕ := ([0,2,4,6,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2206_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,11),(0,12),(0,15),(2,4),(2,6),(2,8),(2,11),(2,12),(2,15),(4,6),(4,8),(4,11),(4,12),(4,15),(6,8),(6,11),(6,12),(6,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2207_q : Finset ℕ := ([0,2,4,6,8,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2207_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(0,15),(2,4),(2,6),(2,8),(2,11),(2,13),(2,15),(4,6),(4,8),(4,11),(4,13),(4,15),(6,8),(6,11),(6,13),(6,15),(8,11),(8,13),(8,15),(11,13),(11,15),(13,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates070
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2208_q : Finset ℕ := ([0,2,4,6,9,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2208_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,9),(0,10),(0,12),(0,15),(2,4),(2,6),(2,9),(2,10),(2,12),(2,15),(4,6),(4,9),(4,10),(4,12),(4,15),(6,9),(6,10),(6,12),(6,15),(9,10),(9,12),(9,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2209_q : Finset ℕ := ([0,2,4,6,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2209_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,9),(0,11),(0,12),(0,15),(2,4),(2,6),(2,9),(2,11),(2,12),(2,15),(4,6),(4,9),(4,11),(4,12),(4,15),(6,9),(6,11),(6,12),(6,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2210_q : Finset ℕ := ([0,2,4,6,9,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2210_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(0,15),(2,4),(2,6),(2,9),(2,11),(2,13),(2,15),(4,6),(4,9),(4,11),(4,13),(4,15),(6,9),(6,11),(6,13),(6,15),(9,11),(9,13),(9,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2211_q : Finset ℕ := ([0,2,4,7,8,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2211_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,8),(0,10),(0,12),(0,15),(2,4),(2,7),(2,8),(2,10),(2,12),(2,15),(4,7),(4,8),(4,10),(4,12),(4,15),(7,8),(7,10),(7,12),(7,15),(8,10),(8,12),(8,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2212_q : Finset ℕ := ([0,2,4,7,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2212_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(0,15),(2,4),(2,7),(2,8),(2,10),(2,13),(2,15),(4,7),(4,8),(4,10),(4,13),(4,15),(7,8),(7,10),(7,13),(7,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2213_q : Finset ℕ := ([0,2,4,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2213_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,8),(0,11),(0,12),(0,15),(2,4),(2,7),(2,8),(2,11),(2,12),(2,15),(4,7),(4,8),(4,11),(4,12),(4,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2214_q : Finset ℕ := ([0,2,4,7,9,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2214_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,9),(0,10),(0,12),(0,15),(2,4),(2,7),(2,9),(2,10),(2,12),(2,15),(4,7),(4,9),(4,10),(4,12),(4,15),(7,9),(7,10),(7,12),(7,15),(9,10),(9,12),(9,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2215_q : Finset ℕ := ([0,2,4,7,9,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2215_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,4),(0,7),(0,9),(0,11),(0,12),(0,15),(2,4),(2,7),(2,9),(2,11),(2,12),(2,15),(4,7),(4,9),(4,11),(4,12),(4,15),(7,9),(7,11),(7,12),(7,15),(9,11),(9,12),(9,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2216_q : Finset ℕ := ([0,2,5,6,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2216_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,5),(0,6),(0,8),(0,11),(0,12),(0,15),(2,5),(2,6),(2,8),(2,11),(2,12),(2,15),(5,6),(5,8),(5,11),(5,12),(5,15),(6,8),(6,11),(6,12),(6,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2217_q : Finset ℕ := ([0,2,5,7,8,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2217_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,2),(0,5),(0,7),(0,8),(0,10),(0,13),(0,15),(2,5),(2,7),(2,8),(2,10),(2,13),(2,15),(5,7),(5,8),(5,10),(5,13),(5,15),(7,8),(7,10),(7,13),(7,15),(8,10),(8,13),(8,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2218_q : Finset ℕ := ([0,2,5,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2218_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,2),(0,5),(0,7),(0,8),(0,11),(0,12),(0,15),(2,5),(2,7),(2,8),(2,11),(2,12),(2,15),(5,7),(5,8),(5,11),(5,12),(5,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2219_q : Finset ℕ := ([0,3,4,7,8,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2219_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,3),(0,4),(0,7),(0,8),(0,11),(0,12),(0,15),(3,4),(3,7),(3,8),(3,11),(3,12),(3,15),(4,7),(4,8),(4,11),(4,12),(4,15),(7,8),(7,11),(7,12),(7,15),(8,11),(8,12),(8,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2220_q : Finset ℕ := ([0,1,2,3,4,5,6,7] : List ℕ).toFinset
noncomputable def certificate_2220_edges : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

noncomputable def certificate_2221_q : Finset ℕ := ([0,1,2,3,4,5,6,8] : List ℕ).toFinset
noncomputable def certificate_2221_edges : List (ℕ × ℕ) := [(6,7),(7,8),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,5),(3,6),(3,8),(4,5),(4,6),(4,8),(5,6),(5,8),(6,8)]

noncomputable def certificate_2222_q : Finset ℕ := ([0,1,2,3,4,5,6,9] : List ℕ).toFinset
noncomputable def certificate_2222_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,9),(2,3),(2,4),(2,5),(2,6),(2,9),(3,4),(3,5),(3,6),(3,9),(4,5),(4,6),(4,9),(5,6),(5,9),(6,9)]

noncomputable def certificate_2223_q : Finset ℕ := ([0,1,2,3,4,5,6,10] : List ℕ).toFinset
noncomputable def certificate_2223_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(2,3),(2,4),(2,5),(2,6),(2,10),(3,4),(3,5),(3,6),(3,10),(4,5),(4,6),(4,10),(5,6),(5,10),(6,10)]

noncomputable def certificate_2224_q : Finset ℕ := ([0,1,2,3,4,5,6,11] : List ℕ).toFinset
noncomputable def certificate_2224_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,11),(1,2),(1,3),(1,4),(1,5),(1,6),(1,11),(2,3),(2,4),(2,5),(2,6),(2,11),(3,4),(3,5),(3,6),(3,11),(4,5),(4,6),(4,11),(5,6),(5,11),(6,11)]

noncomputable def certificate_2225_q : Finset ℕ := ([0,1,2,3,4,5,6,12] : List ℕ).toFinset
noncomputable def certificate_2225_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,12),(1,2),(1,3),(1,4),(1,5),(1,6),(1,12),(2,3),(2,4),(2,5),(2,6),(2,12),(3,4),(3,5),(3,6),(3,12),(4,5),(4,6),(4,12),(5,6),(5,12),(6,12)]

noncomputable def certificate_2226_q : Finset ℕ := ([0,1,2,3,4,5,6,13] : List ℕ).toFinset
noncomputable def certificate_2226_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,13),(1,2),(1,3),(1,4),(1,5),(1,6),(1,13),(2,3),(2,4),(2,5),(2,6),(2,13),(3,4),(3,5),(3,6),(3,13),(4,5),(4,6),(4,13),(5,6),(5,13),(6,13)]

noncomputable def certificate_2227_q : Finset ℕ := ([0,1,2,3,4,5,6,14] : List ℕ).toFinset
noncomputable def certificate_2227_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,14),(1,2),(1,3),(1,4),(1,5),(1,6),(1,14),(2,3),(2,4),(2,5),(2,6),(2,14),(3,4),(3,5),(3,6),(3,14),(4,5),(4,6),(4,14),(5,6),(5,14),(6,14)]

noncomputable def certificate_2228_q : Finset ℕ := ([0,1,2,3,4,5,6,15] : List ℕ).toFinset
noncomputable def certificate_2228_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,15),(1,2),(1,3),(1,4),(1,5),(1,6),(1,15),(2,3),(2,4),(2,5),(2,6),(2,15),(3,4),(3,5),(3,6),(3,15),(4,5),(4,6),(4,15),(5,6),(5,15),(6,15)]

noncomputable def certificate_2229_q : Finset ℕ := ([0,1,2,3,4,5,6,16] : List ℕ).toFinset
noncomputable def certificate_2229_edges : List (ℕ × ℕ) := [(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,16),(1,2),(1,3),(1,4),(1,5),(1,6),(1,16),(2,3),(2,4),(2,5),(2,6),(2,16),(3,4),(3,5),(3,6),(3,16),(4,5),(4,6),(4,16),(5,6),(5,16),(6,16)]

noncomputable def certificate_2230_q : Finset ℕ := ([0,1,2,3,4,5,7,9] : List ℕ).toFinset
noncomputable def certificate_2230_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,9),(1,2),(1,3),(1,4),(1,5),(1,7),(1,9),(2,3),(2,4),(2,5),(2,7),(2,9),(3,4),(3,5),(3,7),(3,9),(4,5),(4,7),(4,9),(5,7),(5,9),(7,9)]

noncomputable def certificate_2231_q : Finset ℕ := ([0,1,2,3,4,5,7,10] : List ℕ).toFinset
noncomputable def certificate_2231_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,10),(1,2),(1,3),(1,4),(1,5),(1,7),(1,10),(2,3),(2,4),(2,5),(2,7),(2,10),(3,4),(3,5),(3,7),(3,10),(4,5),(4,7),(4,10),(5,7),(5,10),(7,10)]

noncomputable def certificate_2232_q : Finset ℕ := ([0,1,2,3,4,5,7,11] : List ℕ).toFinset
noncomputable def certificate_2232_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,11),(1,2),(1,3),(1,4),(1,5),(1,7),(1,11),(2,3),(2,4),(2,5),(2,7),(2,11),(3,4),(3,5),(3,7),(3,11),(4,5),(4,7),(4,11),(5,7),(5,11),(7,11)]

noncomputable def certificate_2233_q : Finset ℕ := ([0,1,2,3,4,5,7,12] : List ℕ).toFinset
noncomputable def certificate_2233_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,12),(1,2),(1,3),(1,4),(1,5),(1,7),(1,12),(2,3),(2,4),(2,5),(2,7),(2,12),(3,4),(3,5),(3,7),(3,12),(4,5),(4,7),(4,12),(5,7),(5,12),(7,12)]

noncomputable def certificate_2234_q : Finset ℕ := ([0,1,2,3,4,5,7,13] : List ℕ).toFinset
noncomputable def certificate_2234_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,13),(1,2),(1,3),(1,4),(1,5),(1,7),(1,13),(2,3),(2,4),(2,5),(2,7),(2,13),(3,4),(3,5),(3,7),(3,13),(4,5),(4,7),(4,13),(5,7),(5,13),(7,13)]

noncomputable def certificate_2235_q : Finset ℕ := ([0,1,2,3,4,5,7,14] : List ℕ).toFinset
noncomputable def certificate_2235_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,14),(1,2),(1,3),(1,4),(1,5),(1,7),(1,14),(2,3),(2,4),(2,5),(2,7),(2,14),(3,4),(3,5),(3,7),(3,14),(4,5),(4,7),(4,14),(5,7),(5,14),(7,14)]

noncomputable def certificate_2236_q : Finset ℕ := ([0,1,2,3,4,5,7,15] : List ℕ).toFinset
noncomputable def certificate_2236_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,15),(1,2),(1,3),(1,4),(1,5),(1,7),(1,15),(2,3),(2,4),(2,5),(2,7),(2,15),(3,4),(3,5),(3,7),(3,15),(4,5),(4,7),(4,15),(5,7),(5,15),(7,15)]

noncomputable def certificate_2237_q : Finset ℕ := ([0,1,2,3,4,5,7,16] : List ℕ).toFinset
noncomputable def certificate_2237_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,5),(0,7),(0,16),(1,2),(1,3),(1,4),(1,5),(1,7),(1,16),(2,3),(2,4),(2,5),(2,7),(2,16),(3,4),(3,5),(3,7),(3,16),(4,5),(4,7),(4,16),(5,7),(5,16),(7,16)]

noncomputable def certificate_2238_q : Finset ℕ := ([0,1,2,3,4,5,8,11] : List ℕ).toFinset
noncomputable def certificate_2238_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,11),(1,2),(1,3),(1,4),(1,5),(1,8),(1,11),(2,3),(2,4),(2,5),(2,8),(2,11),(3,4),(3,5),(3,8),(3,11),(4,5),(4,8),(4,11),(5,8),(5,11),(8,11)]

noncomputable def certificate_2239_q : Finset ℕ := ([0,1,2,3,4,5,8,12] : List ℕ).toFinset
noncomputable def certificate_2239_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,12),(1,2),(1,3),(1,4),(1,5),(1,8),(1,12),(2,3),(2,4),(2,5),(2,8),(2,12),(3,4),(3,5),(3,8),(3,12),(4,5),(4,8),(4,12),(5,8),(5,12),(8,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates071
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2240_q : Finset ℕ := ([0,1,2,3,4,5,8,13] : List ℕ).toFinset
noncomputable def certificate_2240_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,13),(1,2),(1,3),(1,4),(1,5),(1,8),(1,13),(2,3),(2,4),(2,5),(2,8),(2,13),(3,4),(3,5),(3,8),(3,13),(4,5),(4,8),(4,13),(5,8),(5,13),(8,13)]

noncomputable def certificate_2241_q : Finset ℕ := ([0,1,2,3,4,5,8,14] : List ℕ).toFinset
noncomputable def certificate_2241_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,14),(1,2),(1,3),(1,4),(1,5),(1,8),(1,14),(2,3),(2,4),(2,5),(2,8),(2,14),(3,4),(3,5),(3,8),(3,14),(4,5),(4,8),(4,14),(5,8),(5,14),(8,14)]

noncomputable def certificate_2242_q : Finset ℕ := ([0,1,2,3,4,5,8,15] : List ℕ).toFinset
noncomputable def certificate_2242_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,15),(1,2),(1,3),(1,4),(1,5),(1,8),(1,15),(2,3),(2,4),(2,5),(2,8),(2,15),(3,4),(3,5),(3,8),(3,15),(4,5),(4,8),(4,15),(5,8),(5,15),(8,15)]

noncomputable def certificate_2243_q : Finset ℕ := ([0,1,2,3,4,5,8,16] : List ℕ).toFinset
noncomputable def certificate_2243_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,5),(0,8),(0,16),(1,2),(1,3),(1,4),(1,5),(1,8),(1,16),(2,3),(2,4),(2,5),(2,8),(2,16),(3,4),(3,5),(3,8),(3,16),(4,5),(4,8),(4,16),(5,8),(5,16),(8,16)]

noncomputable def certificate_2244_q : Finset ℕ := ([0,1,2,3,4,5,9,13] : List ℕ).toFinset
noncomputable def certificate_2244_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,13),(1,2),(1,3),(1,4),(1,5),(1,9),(1,13),(2,3),(2,4),(2,5),(2,9),(2,13),(3,4),(3,5),(3,9),(3,13),(4,5),(4,9),(4,13),(5,9),(5,13),(9,13)]

noncomputable def certificate_2245_q : Finset ℕ := ([0,1,2,3,4,5,9,14] : List ℕ).toFinset
noncomputable def certificate_2245_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,14),(1,2),(1,3),(1,4),(1,5),(1,9),(1,14),(2,3),(2,4),(2,5),(2,9),(2,14),(3,4),(3,5),(3,9),(3,14),(4,5),(4,9),(4,14),(5,9),(5,14),(9,14)]

noncomputable def certificate_2246_q : Finset ℕ := ([0,1,2,3,4,5,9,15] : List ℕ).toFinset
noncomputable def certificate_2246_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,15),(1,2),(1,3),(1,4),(1,5),(1,9),(1,15),(2,3),(2,4),(2,5),(2,9),(2,15),(3,4),(3,5),(3,9),(3,15),(4,5),(4,9),(4,15),(5,9),(5,15),(9,15)]

noncomputable def certificate_2247_q : Finset ℕ := ([0,1,2,3,4,5,9,16] : List ℕ).toFinset
noncomputable def certificate_2247_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,5),(0,9),(0,16),(1,2),(1,3),(1,4),(1,5),(1,9),(1,16),(2,3),(2,4),(2,5),(2,9),(2,16),(3,4),(3,5),(3,9),(3,16),(4,5),(4,9),(4,16),(5,9),(5,16),(9,16)]

noncomputable def certificate_2248_q : Finset ℕ := ([0,1,2,3,4,5,10,15] : List ℕ).toFinset
noncomputable def certificate_2248_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(0,15),(1,2),(1,3),(1,4),(1,5),(1,10),(1,15),(2,3),(2,4),(2,5),(2,10),(2,15),(3,4),(3,5),(3,10),(3,15),(4,5),(4,10),(4,15),(5,10),(5,15),(10,15)]

noncomputable def certificate_2249_q : Finset ℕ := ([0,1,2,3,4,5,10,16] : List ℕ).toFinset
noncomputable def certificate_2249_edges : List (ℕ × ℕ) := [(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,5),(0,10),(0,16),(1,2),(1,3),(1,4),(1,5),(1,10),(1,16),(2,3),(2,4),(2,5),(2,10),(2,16),(3,4),(3,5),(3,10),(3,16),(4,5),(4,10),(4,16),(5,10),(5,16),(10,16)]

noncomputable def certificate_2250_q : Finset ℕ := ([0,1,2,3,4,6,7,9] : List ℕ).toFinset
noncomputable def certificate_2250_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,9),(1,2),(1,3),(1,4),(1,6),(1,7),(1,9),(2,3),(2,4),(2,6),(2,7),(2,9),(3,4),(3,6),(3,7),(3,9),(4,6),(4,7),(4,9),(6,7),(6,9),(7,9)]

noncomputable def certificate_2251_q : Finset ℕ := ([0,1,2,3,4,6,7,10] : List ℕ).toFinset
noncomputable def certificate_2251_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,10),(1,2),(1,3),(1,4),(1,6),(1,7),(1,10),(2,3),(2,4),(2,6),(2,7),(2,10),(3,4),(3,6),(3,7),(3,10),(4,6),(4,7),(4,10),(6,7),(6,10),(7,10)]

noncomputable def certificate_2252_q : Finset ℕ := ([0,1,2,3,4,6,7,11] : List ℕ).toFinset
noncomputable def certificate_2252_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,11),(1,2),(1,3),(1,4),(1,6),(1,7),(1,11),(2,3),(2,4),(2,6),(2,7),(2,11),(3,4),(3,6),(3,7),(3,11),(4,6),(4,7),(4,11),(6,7),(6,11),(7,11)]

noncomputable def certificate_2253_q : Finset ℕ := ([0,1,2,3,4,6,7,12] : List ℕ).toFinset
noncomputable def certificate_2253_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,12),(1,2),(1,3),(1,4),(1,6),(1,7),(1,12),(2,3),(2,4),(2,6),(2,7),(2,12),(3,4),(3,6),(3,7),(3,12),(4,6),(4,7),(4,12),(6,7),(6,12),(7,12)]

noncomputable def certificate_2254_q : Finset ℕ := ([0,1,2,3,4,6,7,13] : List ℕ).toFinset
noncomputable def certificate_2254_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,13),(1,2),(1,3),(1,4),(1,6),(1,7),(1,13),(2,3),(2,4),(2,6),(2,7),(2,13),(3,4),(3,6),(3,7),(3,13),(4,6),(4,7),(4,13),(6,7),(6,13),(7,13)]

noncomputable def certificate_2255_q : Finset ℕ := ([0,1,2,3,4,6,7,14] : List ℕ).toFinset
noncomputable def certificate_2255_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,14),(1,2),(1,3),(1,4),(1,6),(1,7),(1,14),(2,3),(2,4),(2,6),(2,7),(2,14),(3,4),(3,6),(3,7),(3,14),(4,6),(4,7),(4,14),(6,7),(6,14),(7,14)]

noncomputable def certificate_2256_q : Finset ℕ := ([0,1,2,3,4,6,7,15] : List ℕ).toFinset
noncomputable def certificate_2256_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,15),(1,2),(1,3),(1,4),(1,6),(1,7),(1,15),(2,3),(2,4),(2,6),(2,7),(2,15),(3,4),(3,6),(3,7),(3,15),(4,6),(4,7),(4,15),(6,7),(6,15),(7,15)]

noncomputable def certificate_2257_q : Finset ℕ := ([0,1,2,3,4,6,7,16] : List ℕ).toFinset
noncomputable def certificate_2257_edges : List (ℕ × ℕ) := [(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,16),(1,2),(1,3),(1,4),(1,6),(1,7),(1,16),(2,3),(2,4),(2,6),(2,7),(2,16),(3,4),(3,6),(3,7),(3,16),(4,6),(4,7),(4,16),(6,7),(6,16),(7,16)]

noncomputable def certificate_2258_q : Finset ℕ := ([0,1,2,3,4,6,8,10] : List ℕ).toFinset
noncomputable def certificate_2258_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,10),(1,2),(1,3),(1,4),(1,6),(1,8),(1,10),(2,3),(2,4),(2,6),(2,8),(2,10),(3,4),(3,6),(3,8),(3,10),(4,6),(4,8),(4,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_2259_q : Finset ℕ := ([0,1,2,3,4,6,8,11] : List ℕ).toFinset
noncomputable def certificate_2259_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,11),(1,2),(1,3),(1,4),(1,6),(1,8),(1,11),(2,3),(2,4),(2,6),(2,8),(2,11),(3,4),(3,6),(3,8),(3,11),(4,6),(4,8),(4,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_2260_q : Finset ℕ := ([0,1,2,3,4,6,8,12] : List ℕ).toFinset
noncomputable def certificate_2260_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,12),(1,2),(1,3),(1,4),(1,6),(1,8),(1,12),(2,3),(2,4),(2,6),(2,8),(2,12),(3,4),(3,6),(3,8),(3,12),(4,6),(4,8),(4,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_2261_q : Finset ℕ := ([0,1,2,3,4,6,8,13] : List ℕ).toFinset
noncomputable def certificate_2261_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,13),(1,2),(1,3),(1,4),(1,6),(1,8),(1,13),(2,3),(2,4),(2,6),(2,8),(2,13),(3,4),(3,6),(3,8),(3,13),(4,6),(4,8),(4,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_2262_q : Finset ℕ := ([0,1,2,3,4,6,8,14] : List ℕ).toFinset
noncomputable def certificate_2262_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,14),(1,2),(1,3),(1,4),(1,6),(1,8),(1,14),(2,3),(2,4),(2,6),(2,8),(2,14),(3,4),(3,6),(3,8),(3,14),(4,6),(4,8),(4,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_2263_q : Finset ℕ := ([0,1,2,3,4,6,8,15] : List ℕ).toFinset
noncomputable def certificate_2263_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,15),(1,2),(1,3),(1,4),(1,6),(1,8),(1,15),(2,3),(2,4),(2,6),(2,8),(2,15),(3,4),(3,6),(3,8),(3,15),(4,6),(4,8),(4,15),(6,8),(6,15),(8,15)]

noncomputable def certificate_2264_q : Finset ℕ := ([0,1,2,3,4,6,8,16] : List ℕ).toFinset
noncomputable def certificate_2264_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,8),(0,16),(1,2),(1,3),(1,4),(1,6),(1,8),(1,16),(2,3),(2,4),(2,6),(2,8),(2,16),(3,4),(3,6),(3,8),(3,16),(4,6),(4,8),(4,16),(6,8),(6,16),(8,16)]

noncomputable def certificate_2265_q : Finset ℕ := ([0,1,2,3,4,6,9,11] : List ℕ).toFinset
noncomputable def certificate_2265_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,11),(1,2),(1,3),(1,4),(1,6),(1,9),(1,11),(2,3),(2,4),(2,6),(2,9),(2,11),(3,4),(3,6),(3,9),(3,11),(4,6),(4,9),(4,11),(6,9),(6,11),(9,11)]

noncomputable def certificate_2266_q : Finset ℕ := ([0,1,2,3,4,6,9,12] : List ℕ).toFinset
noncomputable def certificate_2266_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,12),(1,2),(1,3),(1,4),(1,6),(1,9),(1,12),(2,3),(2,4),(2,6),(2,9),(2,12),(3,4),(3,6),(3,9),(3,12),(4,6),(4,9),(4,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_2267_q : Finset ℕ := ([0,1,2,3,4,6,9,13] : List ℕ).toFinset
noncomputable def certificate_2267_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,13),(1,2),(1,3),(1,4),(1,6),(1,9),(1,13),(2,3),(2,4),(2,6),(2,9),(2,13),(3,4),(3,6),(3,9),(3,13),(4,6),(4,9),(4,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_2268_q : Finset ℕ := ([0,1,2,3,4,6,9,14] : List ℕ).toFinset
noncomputable def certificate_2268_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,14),(1,2),(1,3),(1,4),(1,6),(1,9),(1,14),(2,3),(2,4),(2,6),(2,9),(2,14),(3,4),(3,6),(3,9),(3,14),(4,6),(4,9),(4,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_2269_q : Finset ℕ := ([0,1,2,3,4,6,9,15] : List ℕ).toFinset
noncomputable def certificate_2269_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,15),(1,2),(1,3),(1,4),(1,6),(1,9),(1,15),(2,3),(2,4),(2,6),(2,9),(2,15),(3,4),(3,6),(3,9),(3,15),(4,6),(4,9),(4,15),(6,9),(6,15),(9,15)]

noncomputable def certificate_2270_q : Finset ℕ := ([0,1,2,3,4,6,9,16] : List ℕ).toFinset
noncomputable def certificate_2270_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,9),(0,16),(1,2),(1,3),(1,4),(1,6),(1,9),(1,16),(2,3),(2,4),(2,6),(2,9),(2,16),(3,4),(3,6),(3,9),(3,16),(4,6),(4,9),(4,16),(6,9),(6,16),(9,16)]

noncomputable def certificate_2271_q : Finset ℕ := ([0,1,2,3,4,6,10,12] : List ℕ).toFinset
noncomputable def certificate_2271_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,12),(1,2),(1,3),(1,4),(1,6),(1,10),(1,12),(2,3),(2,4),(2,6),(2,10),(2,12),(3,4),(3,6),(3,10),(3,12),(4,6),(4,10),(4,12),(6,10),(6,12),(10,12)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2272_q : Finset ℕ := ([0,1,2,3,4,6,10,13] : List ℕ).toFinset
noncomputable def certificate_2272_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,13),(1,2),(1,3),(1,4),(1,6),(1,10),(1,13),(2,3),(2,4),(2,6),(2,10),(2,13),(3,4),(3,6),(3,10),(3,13),(4,6),(4,10),(4,13),(6,10),(6,13),(10,13)]

noncomputable def certificate_2273_q : Finset ℕ := ([0,1,2,3,4,6,10,14] : List ℕ).toFinset
noncomputable def certificate_2273_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,14),(1,2),(1,3),(1,4),(1,6),(1,10),(1,14),(2,3),(2,4),(2,6),(2,10),(2,14),(3,4),(3,6),(3,10),(3,14),(4,6),(4,10),(4,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_2274_q : Finset ℕ := ([0,1,2,3,4,6,10,15] : List ℕ).toFinset
noncomputable def certificate_2274_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,15),(1,2),(1,3),(1,4),(1,6),(1,10),(1,15),(2,3),(2,4),(2,6),(2,10),(2,15),(3,4),(3,6),(3,10),(3,15),(4,6),(4,10),(4,15),(6,10),(6,15),(10,15)]

noncomputable def certificate_2275_q : Finset ℕ := ([0,1,2,3,4,6,10,16] : List ℕ).toFinset
noncomputable def certificate_2275_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,10),(0,16),(1,2),(1,3),(1,4),(1,6),(1,10),(1,16),(2,3),(2,4),(2,6),(2,10),(2,16),(3,4),(3,6),(3,10),(3,16),(4,6),(4,10),(4,16),(6,10),(6,16),(10,16)]

noncomputable def certificate_2276_q : Finset ℕ := ([0,1,2,3,4,6,11,13] : List ℕ).toFinset
noncomputable def certificate_2276_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,13),(1,2),(1,3),(1,4),(1,6),(1,11),(1,13),(2,3),(2,4),(2,6),(2,11),(2,13),(3,4),(3,6),(3,11),(3,13),(4,6),(4,11),(4,13),(6,11),(6,13),(11,13)]

noncomputable def certificate_2277_q : Finset ℕ := ([0,1,2,3,4,6,11,14] : List ℕ).toFinset
noncomputable def certificate_2277_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,14),(1,2),(1,3),(1,4),(1,6),(1,11),(1,14),(2,3),(2,4),(2,6),(2,11),(2,14),(3,4),(3,6),(3,11),(3,14),(4,6),(4,11),(4,14),(6,11),(6,14),(11,14)]

noncomputable def certificate_2278_q : Finset ℕ := ([0,1,2,3,4,6,11,15] : List ℕ).toFinset
noncomputable def certificate_2278_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,15),(1,2),(1,3),(1,4),(1,6),(1,11),(1,15),(2,3),(2,4),(2,6),(2,11),(2,15),(3,4),(3,6),(3,11),(3,15),(4,6),(4,11),(4,15),(6,11),(6,15),(11,15)]

noncomputable def certificate_2279_q : Finset ℕ := ([0,1,2,3,4,6,11,16] : List ℕ).toFinset
noncomputable def certificate_2279_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,11),(0,16),(1,2),(1,3),(1,4),(1,6),(1,11),(1,16),(2,3),(2,4),(2,6),(2,11),(2,16),(3,4),(3,6),(3,11),(3,16),(4,6),(4,11),(4,16),(6,11),(6,16),(11,16)]

noncomputable def certificate_2280_q : Finset ℕ := ([0,1,2,3,4,6,12,14] : List ℕ).toFinset
noncomputable def certificate_2280_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(0,14),(1,2),(1,3),(1,4),(1,6),(1,12),(1,14),(2,3),(2,4),(2,6),(2,12),(2,14),(3,4),(3,6),(3,12),(3,14),(4,6),(4,12),(4,14),(6,12),(6,14),(12,14)]

noncomputable def certificate_2281_q : Finset ℕ := ([0,1,2,3,4,6,12,15] : List ℕ).toFinset
noncomputable def certificate_2281_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(0,15),(1,2),(1,3),(1,4),(1,6),(1,12),(1,15),(2,3),(2,4),(2,6),(2,12),(2,15),(3,4),(3,6),(3,12),(3,15),(4,6),(4,12),(4,15),(6,12),(6,15),(12,15)]

noncomputable def certificate_2282_q : Finset ℕ := ([0,1,2,3,4,6,12,16] : List ℕ).toFinset
noncomputable def certificate_2282_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,12),(0,16),(1,2),(1,3),(1,4),(1,6),(1,12),(1,16),(2,3),(2,4),(2,6),(2,12),(2,16),(3,4),(3,6),(3,12),(3,16),(4,6),(4,12),(4,16),(6,12),(6,16),(12,16)]

noncomputable def certificate_2283_q : Finset ℕ := ([0,1,2,3,4,6,13,15] : List ℕ).toFinset
noncomputable def certificate_2283_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,6),(0,13),(0,15),(1,2),(1,3),(1,4),(1,6),(1,13),(1,15),(2,3),(2,4),(2,6),(2,13),(2,15),(3,4),(3,6),(3,13),(3,15),(4,6),(4,13),(4,15),(6,13),(6,15),(13,15)]

noncomputable def certificate_2284_q : Finset ℕ := ([0,1,2,3,4,6,13,16] : List ℕ).toFinset
noncomputable def certificate_2284_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,13),(0,16),(1,2),(1,3),(1,4),(1,6),(1,13),(1,16),(2,3),(2,4),(2,6),(2,13),(2,16),(3,4),(3,6),(3,13),(3,16),(4,6),(4,13),(4,16),(6,13),(6,16),(13,16)]

noncomputable def certificate_2285_q : Finset ℕ := ([0,1,2,3,4,6,14,16] : List ℕ).toFinset
noncomputable def certificate_2285_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,6),(0,14),(0,16),(1,2),(1,3),(1,4),(1,6),(1,14),(1,16),(2,3),(2,4),(2,6),(2,14),(2,16),(3,4),(3,6),(3,14),(3,16),(4,6),(4,14),(4,16),(6,14),(6,16),(14,16)]

noncomputable def certificate_2286_q : Finset ℕ := ([0,1,2,3,4,7,8,11] : List ℕ).toFinset
noncomputable def certificate_2286_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,11),(1,2),(1,3),(1,4),(1,7),(1,8),(1,11),(2,3),(2,4),(2,7),(2,8),(2,11),(3,4),(3,7),(3,8),(3,11),(4,7),(4,8),(4,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_2287_q : Finset ℕ := ([0,1,2,3,4,7,8,12] : List ℕ).toFinset
noncomputable def certificate_2287_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,12),(1,2),(1,3),(1,4),(1,7),(1,8),(1,12),(2,3),(2,4),(2,7),(2,8),(2,12),(3,4),(3,7),(3,8),(3,12),(4,7),(4,8),(4,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_2288_q : Finset ℕ := ([0,1,2,3,4,7,8,13] : List ℕ).toFinset
noncomputable def certificate_2288_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,13),(1,2),(1,3),(1,4),(1,7),(1,8),(1,13),(2,3),(2,4),(2,7),(2,8),(2,13),(3,4),(3,7),(3,8),(3,13),(4,7),(4,8),(4,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_2289_q : Finset ℕ := ([0,1,2,3,4,7,8,14] : List ℕ).toFinset
noncomputable def certificate_2289_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,14),(1,2),(1,3),(1,4),(1,7),(1,8),(1,14),(2,3),(2,4),(2,7),(2,8),(2,14),(3,4),(3,7),(3,8),(3,14),(4,7),(4,8),(4,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_2290_q : Finset ℕ := ([0,1,2,3,4,7,8,15] : List ℕ).toFinset
noncomputable def certificate_2290_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,15),(1,2),(1,3),(1,4),(1,7),(1,8),(1,15),(2,3),(2,4),(2,7),(2,8),(2,15),(3,4),(3,7),(3,8),(3,15),(4,7),(4,8),(4,15),(7,8),(7,15),(8,15)]

noncomputable def certificate_2291_q : Finset ℕ := ([0,1,2,3,4,7,8,16] : List ℕ).toFinset
noncomputable def certificate_2291_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,7),(0,8),(0,16),(1,2),(1,3),(1,4),(1,7),(1,8),(1,16),(2,3),(2,4),(2,7),(2,8),(2,16),(3,4),(3,7),(3,8),(3,16),(4,7),(4,8),(4,16),(7,8),(7,16),(8,16)]

noncomputable def certificate_2292_q : Finset ℕ := ([0,1,2,3,4,7,9,12] : List ℕ).toFinset
noncomputable def certificate_2292_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,12),(1,2),(1,3),(1,4),(1,7),(1,9),(1,12),(2,3),(2,4),(2,7),(2,9),(2,12),(3,4),(3,7),(3,9),(3,12),(4,7),(4,9),(4,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_2293_q : Finset ℕ := ([0,1,2,3,4,7,9,13] : List ℕ).toFinset
noncomputable def certificate_2293_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,13),(1,2),(1,3),(1,4),(1,7),(1,9),(1,13),(2,3),(2,4),(2,7),(2,9),(2,13),(3,4),(3,7),(3,9),(3,13),(4,7),(4,9),(4,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_2294_q : Finset ℕ := ([0,1,2,3,4,7,9,14] : List ℕ).toFinset
noncomputable def certificate_2294_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,14),(1,2),(1,3),(1,4),(1,7),(1,9),(1,14),(2,3),(2,4),(2,7),(2,9),(2,14),(3,4),(3,7),(3,9),(3,14),(4,7),(4,9),(4,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_2295_q : Finset ℕ := ([0,1,2,3,4,7,9,15] : List ℕ).toFinset
noncomputable def certificate_2295_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,15),(1,2),(1,3),(1,4),(1,7),(1,9),(1,15),(2,3),(2,4),(2,7),(2,9),(2,15),(3,4),(3,7),(3,9),(3,15),(4,7),(4,9),(4,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_2296_q : Finset ℕ := ([0,1,2,3,4,7,9,16] : List ℕ).toFinset
noncomputable def certificate_2296_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,7),(0,9),(0,16),(1,2),(1,3),(1,4),(1,7),(1,9),(1,16),(2,3),(2,4),(2,7),(2,9),(2,16),(3,4),(3,7),(3,9),(3,16),(4,7),(4,9),(4,16),(7,9),(7,16),(9,16)]

noncomputable def certificate_2297_q : Finset ℕ := ([0,1,2,3,4,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2297_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,13),(1,2),(1,3),(1,4),(1,7),(1,10),(1,13),(2,3),(2,4),(2,7),(2,10),(2,13),(3,4),(3,7),(3,10),(3,13),(4,7),(4,10),(4,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_2298_q : Finset ℕ := ([0,1,2,3,4,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2298_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,14),(1,2),(1,3),(1,4),(1,7),(1,10),(1,14),(2,3),(2,4),(2,7),(2,10),(2,14),(3,4),(3,7),(3,10),(3,14),(4,7),(4,10),(4,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2299_q : Finset ℕ := ([0,1,2,3,4,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2299_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,15),(1,2),(1,3),(1,4),(1,7),(1,10),(1,15),(2,3),(2,4),(2,7),(2,10),(2,15),(3,4),(3,7),(3,10),(3,15),(4,7),(4,10),(4,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2300_q : Finset ℕ := ([0,1,2,3,4,7,10,16] : List ℕ).toFinset
noncomputable def certificate_2300_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,7),(0,10),(0,16),(1,2),(1,3),(1,4),(1,7),(1,10),(1,16),(2,3),(2,4),(2,7),(2,10),(2,16),(3,4),(3,7),(3,10),(3,16),(4,7),(4,10),(4,16),(7,10),(7,16),(10,16)]

noncomputable def certificate_2301_q : Finset ℕ := ([0,1,2,3,4,7,11,14] : List ℕ).toFinset
noncomputable def certificate_2301_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(0,14),(1,2),(1,3),(1,4),(1,7),(1,11),(1,14),(2,3),(2,4),(2,7),(2,11),(2,14),(3,4),(3,7),(3,11),(3,14),(4,7),(4,11),(4,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_2302_q : Finset ℕ := ([0,1,2,3,4,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2302_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(0,15),(1,2),(1,3),(1,4),(1,7),(1,11),(1,15),(2,3),(2,4),(2,7),(2,11),(2,15),(3,4),(3,7),(3,11),(3,15),(4,7),(4,11),(4,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2303_q : Finset ℕ := ([0,1,2,3,4,7,11,16] : List ℕ).toFinset
noncomputable def certificate_2303_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,7),(0,11),(0,16),(1,2),(1,3),(1,4),(1,7),(1,11),(1,16),(2,3),(2,4),(2,7),(2,11),(2,16),(3,4),(3,7),(3,11),(3,16),(4,7),(4,11),(4,16),(7,11),(7,16),(11,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates073
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2304_q : Finset ℕ := ([0,1,2,3,4,7,12,15] : List ℕ).toFinset
noncomputable def certificate_2304_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,7),(0,12),(0,15),(1,2),(1,3),(1,4),(1,7),(1,12),(1,15),(2,3),(2,4),(2,7),(2,12),(2,15),(3,4),(3,7),(3,12),(3,15),(4,7),(4,12),(4,15),(7,12),(7,15),(12,15)]

noncomputable def certificate_2305_q : Finset ℕ := ([0,1,2,3,4,7,12,16] : List ℕ).toFinset
noncomputable def certificate_2305_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,7),(0,12),(0,16),(1,2),(1,3),(1,4),(1,7),(1,12),(1,16),(2,3),(2,4),(2,7),(2,12),(2,16),(3,4),(3,7),(3,12),(3,16),(4,7),(4,12),(4,16),(7,12),(7,16),(12,16)]

noncomputable def certificate_2306_q : Finset ℕ := ([0,1,2,3,4,7,13,16] : List ℕ).toFinset
noncomputable def certificate_2306_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,7),(0,13),(0,16),(1,2),(1,3),(1,4),(1,7),(1,13),(1,16),(2,3),(2,4),(2,7),(2,13),(2,16),(3,4),(3,7),(3,13),(3,16),(4,7),(4,13),(4,16),(7,13),(7,16),(13,16)]

noncomputable def certificate_2307_q : Finset ℕ := ([0,1,2,3,4,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2307_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,13),(1,2),(1,3),(1,4),(1,8),(1,9),(1,13),(2,3),(2,4),(2,8),(2,9),(2,13),(3,4),(3,8),(3,9),(3,13),(4,8),(4,9),(4,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2308_q : Finset ℕ := ([0,1,2,3,4,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2308_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,14),(1,2),(1,3),(1,4),(1,8),(1,9),(1,14),(2,3),(2,4),(2,8),(2,9),(2,14),(3,4),(3,8),(3,9),(3,14),(4,8),(4,9),(4,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2309_q : Finset ℕ := ([0,1,2,3,4,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2309_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,15),(1,2),(1,3),(1,4),(1,8),(1,9),(1,15),(2,3),(2,4),(2,8),(2,9),(2,15),(3,4),(3,8),(3,9),(3,15),(4,8),(4,9),(4,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2310_q : Finset ℕ := ([0,1,2,3,4,8,9,16] : List ℕ).toFinset
noncomputable def certificate_2310_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,8),(0,9),(0,16),(1,2),(1,3),(1,4),(1,8),(1,9),(1,16),(2,3),(2,4),(2,8),(2,9),(2,16),(3,4),(3,8),(3,9),(3,16),(4,8),(4,9),(4,16),(8,9),(8,16),(9,16)]

noncomputable def certificate_2311_q : Finset ℕ := ([0,1,2,3,4,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2311_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,4),(0,8),(0,10),(0,14),(1,2),(1,3),(1,4),(1,8),(1,10),(1,14),(2,3),(2,4),(2,8),(2,10),(2,14),(3,4),(3,8),(3,10),(3,14),(4,8),(4,10),(4,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2312_q : Finset ℕ := ([0,1,2,3,4,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2312_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,8),(0,10),(0,15),(1,2),(1,3),(1,4),(1,8),(1,10),(1,15),(2,3),(2,4),(2,8),(2,10),(2,15),(3,4),(3,8),(3,10),(3,15),(4,8),(4,10),(4,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2313_q : Finset ℕ := ([0,1,2,3,4,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2313_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,8),(0,10),(0,16),(1,2),(1,3),(1,4),(1,8),(1,10),(1,16),(2,3),(2,4),(2,8),(2,10),(2,16),(3,4),(3,8),(3,10),(3,16),(4,8),(4,10),(4,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2314_q : Finset ℕ := ([0,1,2,3,4,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2314_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,8),(0,11),(0,15),(1,2),(1,3),(1,4),(1,8),(1,11),(1,15),(2,3),(2,4),(2,8),(2,11),(2,15),(3,4),(3,8),(3,11),(3,15),(4,8),(4,11),(4,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2315_q : Finset ℕ := ([0,1,2,3,4,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2315_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,8),(0,11),(0,16),(1,2),(1,3),(1,4),(1,8),(1,11),(1,16),(2,3),(2,4),(2,8),(2,11),(2,16),(3,4),(3,8),(3,11),(3,16),(4,8),(4,11),(4,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2316_q : Finset ℕ := ([0,1,2,3,4,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2316_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,8),(0,12),(0,16),(1,2),(1,3),(1,4),(1,8),(1,12),(1,16),(2,3),(2,4),(2,8),(2,12),(2,16),(3,4),(3,8),(3,12),(3,16),(4,8),(4,12),(4,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2317_q : Finset ℕ := ([0,1,2,3,4,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2317_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,4),(0,9),(0,10),(0,15),(1,2),(1,3),(1,4),(1,9),(1,10),(1,15),(2,3),(2,4),(2,9),(2,10),(2,15),(3,4),(3,9),(3,10),(3,15),(4,9),(4,10),(4,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2318_q : Finset ℕ := ([0,1,2,3,4,9,10,16] : List ℕ).toFinset

noncomputable def certificate_2318_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,9),(0,10),(0,16),(1,2),(1,3),(1,4),(1,9),(1,10),(1,16),(2,3),(2,4),(2,9),(2,10),(2,16),(3,4),(3,9),(3,10),(3,16),(4,9),(4,10),(4,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2318_E : List (ℕ × ℕ) := certificate_2318_edges

noncomputable def certificate_2318_part_1_E : List (ℕ × ℕ) := certificate_2318_E

noncomputable def certificate_2318_part_2_E : List (ℕ × ℕ) := certificate_2318_part_1_E

noncomputable def certificate_2318_part_3_E : List (ℕ × ℕ) := certificate_2318_part_2_E

noncomputable def certificate_2318_part_4_E : List (ℕ × ℕ) := certificate_2318_part_3_E

noncomputable def certificate_2318_part_5_E : List (ℕ × ℕ) := certificate_2318_part_4_E

noncomputable def certificate_2318_part_6_E : List (ℕ × ℕ) := certificate_2318_part_5_E

noncomputable def certificate_2318_part_7_E : List (ℕ × ℕ) := certificate_2318_part_6_E

noncomputable def certificate_2318_part_8_E : List (ℕ × ℕ) := certificate_2318_part_7_E

noncomputable def certificate_2318_part_9_E : List (ℕ × ℕ) := certificate_2318_part_8_E

noncomputable def certificate_2318_part_10_E : List (ℕ × ℕ) := certificate_2318_part_9_E

noncomputable def certificate_2318_part_11_E : List (ℕ × ℕ) := certificate_2318_part_10_E

noncomputable def certificate_2318_part_14_E : List (ℕ × ℕ) := certificate_2318_part_11_E

noncomputable def certificate_2318_part_19_E : List (ℕ × ℕ) := certificate_2318_part_14_E

noncomputable def certificate_2318_part_23_E : List (ℕ × ℕ) := certificate_2318_part_19_E

noncomputable def certificate_2318_part_24_E : List (ℕ × ℕ) := certificate_2318_part_23_E

noncomputable def certificate_2318_part_25_E : List (ℕ × ℕ) := certificate_2318_part_24_E

noncomputable def certificate_2318_part_26_E : List (ℕ × ℕ) := certificate_2318_part_25_E

noncomputable def certificate_2318_part_27_E : List (ℕ × ℕ) := certificate_2318_part_26_E

noncomputable def certificate_2318_part_28_E : List (ℕ × ℕ) := certificate_2318_part_27_E

noncomputable def certificate_2318_part_29_E : List (ℕ × ℕ) := certificate_2318_part_28_E

noncomputable def certificate_2318_part_39_E : List (ℕ × ℕ) := certificate_2318_part_29_E

noncomputable def certificate_2318_part_41_E : List (ℕ × ℕ) := certificate_2318_part_39_E

noncomputable def certificate_2318_part_46_E : List (ℕ × ℕ) := certificate_2318_part_41_E

noncomputable def certificate_2318_part_47_E : List (ℕ × ℕ) := certificate_2318_part_46_E

noncomputable def certificate_2318_part_56_E : List (ℕ × ℕ) := certificate_2318_part_47_E

noncomputable def certificate_2318_part_61_E : List (ℕ × ℕ) := certificate_2318_part_56_E

noncomputable def certificate_2318_part_73_E : List (ℕ × ℕ) := certificate_2318_part_61_E

noncomputable def certificate_2318_part_77_E : List (ℕ × ℕ) := certificate_2318_part_73_E

noncomputable def certificate_2319_q : Finset ℕ := ([0,1,2,3,4,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2319_edges : List (ℕ × ℕ) := [(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,4),(0,9),(0,11),(0,16),(1,2),(1,3),(1,4),(1,9),(1,11),(1,16),(2,3),(2,4),(2,9),(2,11),(2,16),(3,4),(3,9),(3,11),(3,16),(4,9),(4,11),(4,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2320_q : Finset ℕ := ([0,1,2,3,5,6,8,10] : List ℕ).toFinset
noncomputable def certificate_2320_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,10),(1,2),(1,3),(1,5),(1,6),(1,8),(1,10),(2,3),(2,5),(2,6),(2,8),(2,10),(3,5),(3,6),(3,8),(3,10),(5,6),(5,8),(5,10),(6,8),(6,10),(8,10)]

noncomputable def certificate_2321_q : Finset ℕ := ([0,1,2,3,5,6,8,11] : List ℕ).toFinset
noncomputable def certificate_2321_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,11),(1,2),(1,3),(1,5),(1,6),(1,8),(1,11),(2,3),(2,5),(2,6),(2,8),(2,11),(3,5),(3,6),(3,8),(3,11),(5,6),(5,8),(5,11),(6,8),(6,11),(8,11)]

noncomputable def certificate_2322_q : Finset ℕ := ([0,1,2,3,5,6,8,12] : List ℕ).toFinset
noncomputable def certificate_2322_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,12),(1,2),(1,3),(1,5),(1,6),(1,8),(1,12),(2,3),(2,5),(2,6),(2,8),(2,12),(3,5),(3,6),(3,8),(3,12),(5,6),(5,8),(5,12),(6,8),(6,12),(8,12)]

noncomputable def certificate_2323_q : Finset ℕ := ([0,1,2,3,5,6,8,13] : List ℕ).toFinset
noncomputable def certificate_2323_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,13),(1,2),(1,3),(1,5),(1,6),(1,8),(1,13),(2,3),(2,5),(2,6),(2,8),(2,13),(3,5),(3,6),(3,8),(3,13),(5,6),(5,8),(5,13),(6,8),(6,13),(8,13)]

noncomputable def certificate_2324_q : Finset ℕ := ([0,1,2,3,5,6,8,14] : List ℕ).toFinset
noncomputable def certificate_2324_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,14),(1,2),(1,3),(1,5),(1,6),(1,8),(1,14),(2,3),(2,5),(2,6),(2,8),(2,14),(3,5),(3,6),(3,8),(3,14),(5,6),(5,8),(5,14),(6,8),(6,14),(8,14)]

noncomputable def certificate_2325_q : Finset ℕ := ([0,1,2,3,5,6,8,15] : List ℕ).toFinset
noncomputable def certificate_2325_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,15),(1,2),(1,3),(1,5),(1,6),(1,8),(1,15),(2,3),(2,5),(2,6),(2,8),(2,15),(3,5),(3,6),(3,8),(3,15),(5,6),(5,8),(5,15),(6,8),(6,15),(8,15)]

noncomputable def certificate_2326_q : Finset ℕ := ([0,1,2,3,5,6,8,16] : List ℕ).toFinset
noncomputable def certificate_2326_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,6),(0,8),(0,16),(1,2),(1,3),(1,5),(1,6),(1,8),(1,16),(2,3),(2,5),(2,6),(2,8),(2,16),(3,5),(3,6),(3,8),(3,16),(5,6),(5,8),(5,16),(6,8),(6,16),(8,16)]

noncomputable def certificate_2327_q : Finset ℕ := ([0,1,2,3,5,6,9,12] : List ℕ).toFinset
noncomputable def certificate_2327_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,12),(1,2),(1,3),(1,5),(1,6),(1,9),(1,12),(2,3),(2,5),(2,6),(2,9),(2,12),(3,5),(3,6),(3,9),(3,12),(5,6),(5,9),(5,12),(6,9),(6,12),(9,12)]

noncomputable def certificate_2328_q : Finset ℕ := ([0,1,2,3,5,6,9,13] : List ℕ).toFinset
noncomputable def certificate_2328_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,13),(1,2),(1,3),(1,5),(1,6),(1,9),(1,13),(2,3),(2,5),(2,6),(2,9),(2,13),(3,5),(3,6),(3,9),(3,13),(5,6),(5,9),(5,13),(6,9),(6,13),(9,13)]

noncomputable def certificate_2329_q : Finset ℕ := ([0,1,2,3,5,6,9,14] : List ℕ).toFinset
noncomputable def certificate_2329_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,14),(1,2),(1,3),(1,5),(1,6),(1,9),(1,14),(2,3),(2,5),(2,6),(2,9),(2,14),(3,5),(3,6),(3,9),(3,14),(5,6),(5,9),(5,14),(6,9),(6,14),(9,14)]

noncomputable def certificate_2330_q : Finset ℕ := ([0,1,2,3,5,6,9,15] : List ℕ).toFinset
noncomputable def certificate_2330_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,15),(1,2),(1,3),(1,5),(1,6),(1,9),(1,15),(2,3),(2,5),(2,6),(2,9),(2,15),(3,5),(3,6),(3,9),(3,15),(5,6),(5,9),(5,15),(6,9),(6,15),(9,15)]

noncomputable def certificate_2331_q : Finset ℕ := ([0,1,2,3,5,6,9,16] : List ℕ).toFinset
noncomputable def certificate_2331_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,6),(0,9),(0,16),(1,2),(1,3),(1,5),(1,6),(1,9),(1,16),(2,3),(2,5),(2,6),(2,9),(2,16),(3,5),(3,6),(3,9),(3,16),(5,6),(5,9),(5,16),(6,9),(6,16),(9,16)]

noncomputable def certificate_2332_q : Finset ℕ := ([0,1,2,3,5,6,10,14] : List ℕ).toFinset
noncomputable def certificate_2332_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(0,14),(1,2),(1,3),(1,5),(1,6),(1,10),(1,14),(2,3),(2,5),(2,6),(2,10),(2,14),(3,5),(3,6),(3,10),(3,14),(5,6),(5,10),(5,14),(6,10),(6,14),(10,14)]

noncomputable def certificate_2333_q : Finset ℕ := ([0,1,2,3,5,6,10,15] : List ℕ).toFinset
noncomputable def certificate_2333_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(0,15),(1,2),(1,3),(1,5),(1,6),(1,10),(1,15),(2,3),(2,5),(2,6),(2,10),(2,15),(3,5),(3,6),(3,10),(3,15),(5,6),(5,10),(5,15),(6,10),(6,15),(10,15)]

noncomputable def certificate_2334_q : Finset ℕ := ([0,1,2,3,5,6,10,16] : List ℕ).toFinset
noncomputable def certificate_2334_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,6),(0,10),(0,16),(1,2),(1,3),(1,5),(1,6),(1,10),(1,16),(2,3),(2,5),(2,6),(2,10),(2,16),(3,5),(3,6),(3,10),(3,16),(5,6),(5,10),(5,16),(6,10),(6,16),(10,16)]

noncomputable def certificate_2335_q : Finset ℕ := ([0,1,2,3,5,6,11,16] : List ℕ).toFinset
noncomputable def certificate_2335_edges : List (ℕ × ℕ) := [(3,4),(4,5),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,6),(0,11),(0,16),(1,2),(1,3),(1,5),(1,6),(1,11),(1,16),(2,3),(2,5),(2,6),(2,11),(2,16),(3,5),(3,6),(3,11),(3,16),(5,6),(5,11),(5,16),(6,11),(6,16),(11,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates074
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2336_q : Finset ℕ := ([0,1,2,3,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_2336_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,11),(1,2),(1,3),(1,5),(1,7),(1,8),(1,11),(2,3),(2,5),(2,7),(2,8),(2,11),(3,5),(3,7),(3,8),(3,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_2337_q : Finset ℕ := ([0,1,2,3,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_2337_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,12),(1,2),(1,3),(1,5),(1,7),(1,8),(1,12),(2,3),(2,5),(2,7),(2,8),(2,12),(3,5),(3,7),(3,8),(3,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_2338_q : Finset ℕ := ([0,1,2,3,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_2338_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,13),(1,2),(1,3),(1,5),(1,7),(1,8),(1,13),(2,3),(2,5),(2,7),(2,8),(2,13),(3,5),(3,7),(3,8),(3,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_2339_q : Finset ℕ := ([0,1,2,3,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_2339_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,14),(1,2),(1,3),(1,5),(1,7),(1,8),(1,14),(2,3),(2,5),(2,7),(2,8),(2,14),(3,5),(3,7),(3,8),(3,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_2340_q : Finset ℕ := ([0,1,2,3,5,7,8,15] : List ℕ).toFinset
noncomputable def certificate_2340_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,15),(1,2),(1,3),(1,5),(1,7),(1,8),(1,15),(2,3),(2,5),(2,7),(2,8),(2,15),(3,5),(3,7),(3,8),(3,15),(5,7),(5,8),(5,15),(7,8),(7,15),(8,15)]

noncomputable def certificate_2341_q : Finset ℕ := ([0,1,2,3,5,7,8,16] : List ℕ).toFinset
noncomputable def certificate_2341_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(0,16),(1,2),(1,3),(1,5),(1,7),(1,8),(1,16),(2,3),(2,5),(2,7),(2,8),(2,16),(3,5),(3,7),(3,8),(3,16),(5,7),(5,8),(5,16),(7,8),(7,16),(8,16)]

noncomputable def certificate_2342_q : Finset ℕ := ([0,1,2,3,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_2342_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,11),(1,2),(1,3),(1,5),(1,7),(1,9),(1,11),(2,3),(2,5),(2,7),(2,9),(2,11),(3,5),(3,7),(3,9),(3,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_2343_q : Finset ℕ := ([0,1,2,3,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_2343_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,12),(1,2),(1,3),(1,5),(1,7),(1,9),(1,12),(2,3),(2,5),(2,7),(2,9),(2,12),(3,5),(3,7),(3,9),(3,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_2344_q : Finset ℕ := ([0,1,2,3,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_2344_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,13),(1,2),(1,3),(1,5),(1,7),(1,9),(1,13),(2,3),(2,5),(2,7),(2,9),(2,13),(3,5),(3,7),(3,9),(3,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_2345_q : Finset ℕ := ([0,1,2,3,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_2345_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,14),(1,2),(1,3),(1,5),(1,7),(1,9),(1,14),(2,3),(2,5),(2,7),(2,9),(2,14),(3,5),(3,7),(3,9),(3,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_2346_q : Finset ℕ := ([0,1,2,3,5,7,9,15] : List ℕ).toFinset
noncomputable def certificate_2346_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,15),(1,2),(1,3),(1,5),(1,7),(1,9),(1,15),(2,3),(2,5),(2,7),(2,9),(2,15),(3,5),(3,7),(3,9),(3,15),(5,7),(5,9),(5,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_2347_q : Finset ℕ := ([0,1,2,3,5,7,9,16] : List ℕ).toFinset
noncomputable def certificate_2347_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,9),(0,16),(1,2),(1,3),(1,5),(1,7),(1,9),(1,16),(2,3),(2,5),(2,7),(2,9),(2,16),(3,5),(3,7),(3,9),(3,16),(5,7),(5,9),(5,16),(7,9),(7,16),(9,16)]

noncomputable def certificate_2348_q : Finset ℕ := ([0,1,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_2348_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(1,2),(1,3),(1,5),(1,7),(1,10),(1,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_2349_q : Finset ℕ := ([0,1,2,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2349_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(1,2),(1,3),(1,5),(1,7),(1,10),(1,13),(2,3),(2,5),(2,7),(2,10),(2,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_2350_q : Finset ℕ := ([0,1,2,3,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2350_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,14),(1,2),(1,3),(1,5),(1,7),(1,10),(1,14),(2,3),(2,5),(2,7),(2,10),(2,14),(3,5),(3,7),(3,10),(3,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2351_q : Finset ℕ := ([0,1,2,3,5,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2351_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,15),(1,2),(1,3),(1,5),(1,7),(1,10),(1,15),(2,3),(2,5),(2,7),(2,10),(2,15),(3,5),(3,7),(3,10),(3,15),(5,7),(5,10),(5,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2352_q : Finset ℕ := ([0,1,2,3,5,7,10,16] : List ℕ).toFinset
noncomputable def certificate_2352_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,10),(0,16),(1,2),(1,3),(1,5),(1,7),(1,10),(1,16),(2,3),(2,5),(2,7),(2,10),(2,16),(3,5),(3,7),(3,10),(3,16),(5,7),(5,10),(5,16),(7,10),(7,16),(10,16)]

noncomputable def certificate_2353_q : Finset ℕ := ([0,1,2,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_2353_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(1,2),(1,3),(1,5),(1,7),(1,11),(1,13),(2,3),(2,5),(2,7),(2,11),(2,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_2354_q : Finset ℕ := ([0,1,2,3,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_2354_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,14),(1,2),(1,3),(1,5),(1,7),(1,11),(1,14),(2,3),(2,5),(2,7),(2,11),(2,14),(3,5),(3,7),(3,11),(3,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_2355_q : Finset ℕ := ([0,1,2,3,5,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2355_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,15),(1,2),(1,3),(1,5),(1,7),(1,11),(1,15),(2,3),(2,5),(2,7),(2,11),(2,15),(3,5),(3,7),(3,11),(3,15),(5,7),(5,11),(5,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2356_q : Finset ℕ := ([0,1,2,3,5,7,11,16] : List ℕ).toFinset
noncomputable def certificate_2356_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,11),(0,16),(1,2),(1,3),(1,5),(1,7),(1,11),(1,16),(2,3),(2,5),(2,7),(2,11),(2,16),(3,5),(3,7),(3,11),(3,16),(5,7),(5,11),(5,16),(7,11),(7,16),(11,16)]

noncomputable def certificate_2357_q : Finset ℕ := ([0,1,2,3,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_2357_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(0,14),(1,2),(1,3),(1,5),(1,7),(1,12),(1,14),(2,3),(2,5),(2,7),(2,12),(2,14),(3,5),(3,7),(3,12),(3,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_2358_q : Finset ℕ := ([0,1,2,3,5,7,12,15] : List ℕ).toFinset
noncomputable def certificate_2358_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(0,15),(1,2),(1,3),(1,5),(1,7),(1,12),(1,15),(2,3),(2,5),(2,7),(2,12),(2,15),(3,5),(3,7),(3,12),(3,15),(5,7),(5,12),(5,15),(7,12),(7,15),(12,15)]

noncomputable def certificate_2359_q : Finset ℕ := ([0,1,2,3,5,7,12,16] : List ℕ).toFinset
noncomputable def certificate_2359_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,12),(0,16),(1,2),(1,3),(1,5),(1,7),(1,12),(1,16),(2,3),(2,5),(2,7),(2,12),(2,16),(3,5),(3,7),(3,12),(3,16),(5,7),(5,12),(5,16),(7,12),(7,16),(12,16)]

noncomputable def certificate_2360_q : Finset ℕ := ([0,1,2,3,5,7,13,15] : List ℕ).toFinset
noncomputable def certificate_2360_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,7),(0,13),(0,15),(1,2),(1,3),(1,5),(1,7),(1,13),(1,15),(2,3),(2,5),(2,7),(2,13),(2,15),(3,5),(3,7),(3,13),(3,15),(5,7),(5,13),(5,15),(7,13),(7,15),(13,15)]

noncomputable def certificate_2361_q : Finset ℕ := ([0,1,2,3,5,7,13,16] : List ℕ).toFinset
noncomputable def certificate_2361_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,13),(0,16),(1,2),(1,3),(1,5),(1,7),(1,13),(1,16),(2,3),(2,5),(2,7),(2,13),(2,16),(3,5),(3,7),(3,13),(3,16),(5,7),(5,13),(5,16),(7,13),(7,16),(13,16)]

noncomputable def certificate_2362_q : Finset ℕ := ([0,1,2,3,5,7,14,16] : List ℕ).toFinset
noncomputable def certificate_2362_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,7),(0,14),(0,16),(1,2),(1,3),(1,5),(1,7),(1,14),(1,16),(2,3),(2,5),(2,7),(2,14),(2,16),(3,5),(3,7),(3,14),(3,16),(5,7),(5,14),(5,16),(7,14),(7,16),(14,16)]

noncomputable def certificate_2363_q : Finset ℕ := ([0,1,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2363_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(1,2),(1,3),(1,5),(1,8),(1,9),(1,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2364_q : Finset ℕ := ([0,1,2,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2364_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,13),(1,2),(1,3),(1,5),(1,8),(1,9),(1,13),(2,3),(2,5),(2,8),(2,9),(2,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2365_q : Finset ℕ := ([0,1,2,3,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2365_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,14),(1,2),(1,3),(1,5),(1,8),(1,9),(1,14),(2,3),(2,5),(2,8),(2,9),(2,14),(3,5),(3,8),(3,9),(3,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2366_q : Finset ℕ := ([0,1,2,3,5,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2366_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,15),(1,2),(1,3),(1,5),(1,8),(1,9),(1,15),(2,3),(2,5),(2,8),(2,9),(2,15),(3,5),(3,8),(3,9),(3,15),(5,8),(5,9),(5,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2367_q : Finset ℕ := ([0,1,2,3,5,8,9,16] : List ℕ).toFinset
noncomputable def certificate_2367_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,8),(0,9),(0,16),(1,2),(1,3),(1,5),(1,8),(1,9),(1,16),(2,3),(2,5),(2,8),(2,9),(2,16),(3,5),(3,8),(3,9),(3,16),(5,8),(5,9),(5,16),(8,9),(8,16),(9,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates075
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2368_q : Finset ℕ := ([0,1,2,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2368_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(1,2),(1,3),(1,5),(1,8),(1,10),(1,13),(2,3),(2,5),(2,8),(2,10),(2,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2369_q : Finset ℕ := ([0,1,2,3,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2369_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,14),(1,2),(1,3),(1,5),(1,8),(1,10),(1,14),(2,3),(2,5),(2,8),(2,10),(2,14),(3,5),(3,8),(3,10),(3,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2370_q : Finset ℕ := ([0,1,2,3,5,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2370_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,15),(1,2),(1,3),(1,5),(1,8),(1,10),(1,15),(2,3),(2,5),(2,8),(2,10),(2,15),(3,5),(3,8),(3,10),(3,15),(5,8),(5,10),(5,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2371_q : Finset ℕ := ([0,1,2,3,5,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2371_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,8),(0,10),(0,16),(1,2),(1,3),(1,5),(1,8),(1,10),(1,16),(2,3),(2,5),(2,8),(2,10),(2,16),(3,5),(3,8),(3,10),(3,16),(5,8),(5,10),(5,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2372_q : Finset ℕ := ([0,1,2,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2372_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(1,2),(1,3),(1,5),(1,8),(1,11),(1,13),(2,3),(2,5),(2,8),(2,11),(2,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2373_q : Finset ℕ := ([0,1,2,3,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2373_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,14),(1,2),(1,3),(1,5),(1,8),(1,11),(1,14),(2,3),(2,5),(2,8),(2,11),(2,14),(3,5),(3,8),(3,11),(3,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2374_q : Finset ℕ := ([0,1,2,3,5,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2374_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,15),(1,2),(1,3),(1,5),(1,8),(1,11),(1,15),(2,3),(2,5),(2,8),(2,11),(2,15),(3,5),(3,8),(3,11),(3,15),(5,8),(5,11),(5,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2375_q : Finset ℕ := ([0,1,2,3,5,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2375_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,8),(0,11),(0,16),(1,2),(1,3),(1,5),(1,8),(1,11),(1,16),(2,3),(2,5),(2,8),(2,11),(2,16),(3,5),(3,8),(3,11),(3,16),(5,8),(5,11),(5,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2376_q : Finset ℕ := ([0,1,2,3,5,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2376_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(0,14),(1,2),(1,3),(1,5),(1,8),(1,12),(1,14),(2,3),(2,5),(2,8),(2,12),(2,14),(3,5),(3,8),(3,12),(3,14),(5,8),(5,12),(5,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2377_q : Finset ℕ := ([0,1,2,3,5,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2377_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(0,15),(1,2),(1,3),(1,5),(1,8),(1,12),(1,15),(2,3),(2,5),(2,8),(2,12),(2,15),(3,5),(3,8),(3,12),(3,15),(5,8),(5,12),(5,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2378_q : Finset ℕ := ([0,1,2,3,5,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2378_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,8),(0,12),(0,16),(1,2),(1,3),(1,5),(1,8),(1,12),(1,16),(2,3),(2,5),(2,8),(2,12),(2,16),(3,5),(3,8),(3,12),(3,16),(5,8),(5,12),(5,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2379_q : Finset ℕ := ([0,1,2,3,5,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2379_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,8),(0,13),(0,15),(1,2),(1,3),(1,5),(1,8),(1,13),(1,15),(2,3),(2,5),(2,8),(2,13),(2,15),(3,5),(3,8),(3,13),(3,15),(5,8),(5,13),(5,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2380_q : Finset ℕ := ([0,1,2,3,5,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2380_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,8),(0,13),(0,16),(1,2),(1,3),(1,5),(1,8),(1,13),(1,16),(2,3),(2,5),(2,8),(2,13),(2,16),(3,5),(3,8),(3,13),(3,16),(5,8),(5,13),(5,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2381_q : Finset ℕ := ([0,1,2,3,5,8,14,16] : List ℕ).toFinset
noncomputable def certificate_2381_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,8),(0,14),(0,16),(1,2),(1,3),(1,5),(1,8),(1,14),(1,16),(2,3),(2,5),(2,8),(2,14),(2,16),(3,5),(3,8),(3,14),(3,16),(5,8),(5,14),(5,16),(8,14),(8,16),(14,16)]

noncomputable def certificate_2382_q : Finset ℕ := ([0,1,2,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2382_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(1,2),(1,3),(1,5),(1,9),(1,10),(1,13),(2,3),(2,5),(2,9),(2,10),(2,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2383_q : Finset ℕ := ([0,1,2,3,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2383_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,14),(1,2),(1,3),(1,5),(1,9),(1,10),(1,14),(2,3),(2,5),(2,9),(2,10),(2,14),(3,5),(3,9),(3,10),(3,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2384_q : Finset ℕ := ([0,1,2,3,5,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2384_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,15),(1,2),(1,3),(1,5),(1,9),(1,10),(1,15),(2,3),(2,5),(2,9),(2,10),(2,15),(3,5),(3,9),(3,10),(3,15),(5,9),(5,10),(5,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2385_q : Finset ℕ := ([0,1,2,3,5,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2385_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,9),(0,10),(0,16),(1,2),(1,3),(1,5),(1,9),(1,10),(1,16),(2,3),(2,5),(2,9),(2,10),(2,16),(3,5),(3,9),(3,10),(3,16),(5,9),(5,10),(5,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2386_q : Finset ℕ := ([0,1,2,3,5,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2386_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(0,14),(1,2),(1,3),(1,5),(1,9),(1,11),(1,14),(2,3),(2,5),(2,9),(2,11),(2,14),(3,5),(3,9),(3,11),(3,14),(5,9),(5,11),(5,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2387_q : Finset ℕ := ([0,1,2,3,5,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2387_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(0,15),(1,2),(1,3),(1,5),(1,9),(1,11),(1,15),(2,3),(2,5),(2,9),(2,11),(2,15),(3,5),(3,9),(3,11),(3,15),(5,9),(5,11),(5,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2388_q : Finset ℕ := ([0,1,2,3,5,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2388_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,9),(0,11),(0,16),(1,2),(1,3),(1,5),(1,9),(1,11),(1,16),(2,3),(2,5),(2,9),(2,11),(2,16),(3,5),(3,9),(3,11),(3,16),(5,9),(5,11),(5,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2389_q : Finset ℕ := ([0,1,2,3,5,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2389_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,12),(0,15),(1,2),(1,3),(1,5),(1,9),(1,12),(1,15),(2,3),(2,5),(2,9),(2,12),(2,15),(3,5),(3,9),(3,12),(3,15),(5,9),(5,12),(5,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2390_q : Finset ℕ := ([0,1,2,3,5,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2390_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,9),(0,12),(0,16),(1,2),(1,3),(1,5),(1,9),(1,12),(1,16),(2,3),(2,5),(2,9),(2,12),(2,16),(3,5),(3,9),(3,12),(3,16),(5,9),(5,12),(5,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2391_q : Finset ℕ := ([0,1,2,3,5,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2391_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,9),(0,13),(0,15),(1,2),(1,3),(1,5),(1,9),(1,13),(1,15),(2,3),(2,5),(2,9),(2,13),(2,15),(3,5),(3,9),(3,13),(3,15),(5,9),(5,13),(5,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2392_q : Finset ℕ := ([0,1,2,3,5,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2392_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,9),(0,13),(0,16),(1,2),(1,3),(1,5),(1,9),(1,13),(1,16),(2,3),(2,5),(2,9),(2,13),(2,16),(3,5),(3,9),(3,13),(3,16),(5,9),(5,13),(5,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2393_q : Finset ℕ := ([0,1,2,3,5,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2393_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,9),(0,14),(0,16),(1,2),(1,3),(1,5),(1,9),(1,14),(1,16),(2,3),(2,5),(2,9),(2,14),(2,16),(3,5),(3,9),(3,14),(3,16),(5,9),(5,14),(5,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2394_q : Finset ℕ := ([0,1,2,3,5,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2394_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,5),(0,10),(0,11),(0,14),(1,2),(1,3),(1,5),(1,10),(1,11),(1,14),(2,3),(2,5),(2,10),(2,11),(2,14),(3,5),(3,10),(3,11),(3,14),(5,10),(5,11),(5,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2395_q : Finset ℕ := ([0,1,2,3,5,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2395_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,10),(0,11),(0,15),(1,2),(1,3),(1,5),(1,10),(1,11),(1,15),(2,3),(2,5),(2,10),(2,11),(2,15),(3,5),(3,10),(3,11),(3,15),(5,10),(5,11),(5,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2396_q : Finset ℕ := ([0,1,2,3,5,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2396_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,10),(0,11),(0,16),(1,2),(1,3),(1,5),(1,10),(1,11),(1,16),(2,3),(2,5),(2,10),(2,11),(2,16),(3,5),(3,10),(3,11),(3,16),(5,10),(5,11),(5,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2397_q : Finset ℕ := ([0,1,2,3,5,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2397_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,10),(0,12),(0,15),(1,2),(1,3),(1,5),(1,10),(1,12),(1,15),(2,3),(2,5),(2,10),(2,12),(2,15),(3,5),(3,10),(3,12),(3,15),(5,10),(5,12),(5,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2398_q : Finset ℕ := ([0,1,2,3,5,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2398_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,10),(0,12),(0,16),(1,2),(1,3),(1,5),(1,10),(1,12),(1,16),(2,3),(2,5),(2,10),(2,12),(2,16),(3,5),(3,10),(3,12),(3,16),(5,10),(5,12),(5,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2399_q : Finset ℕ := ([0,1,2,3,5,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2399_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,10),(0,13),(0,16),(1,2),(1,3),(1,5),(1,10),(1,13),(1,16),(2,3),(2,5),(2,10),(2,13),(2,16),(3,5),(3,10),(3,13),(3,16),(5,10),(5,13),(5,16),(10,13),(10,16),(13,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates076
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2400_q : Finset ℕ := ([0,1,2,3,5,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2400_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,5),(0,11),(0,12),(0,15),(1,2),(1,3),(1,5),(1,11),(1,12),(1,15),(2,3),(2,5),(2,11),(2,12),(2,15),(3,5),(3,11),(3,12),(3,15),(5,11),(5,12),(5,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2401_q : Finset ℕ := ([0,1,2,3,5,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2401_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,11),(0,12),(0,16),(1,2),(1,3),(1,5),(1,11),(1,12),(1,16),(2,3),(2,5),(2,11),(2,12),(2,16),(3,5),(3,11),(3,12),(3,16),(5,11),(5,12),(5,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2402_q : Finset ℕ := ([0,1,2,3,5,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2402_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,11),(0,13),(0,16),(1,2),(1,3),(1,5),(1,11),(1,13),(1,16),(2,3),(2,5),(2,11),(2,13),(2,16),(3,5),(3,11),(3,13),(3,16),(5,11),(5,13),(5,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2403_q : Finset ℕ := ([0,1,2,3,5,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2403_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,5),(0,12),(0,13),(0,16),(1,2),(1,3),(1,5),(1,12),(1,13),(1,16),(2,3),(2,5),(2,12),(2,13),(2,16),(3,5),(3,12),(3,13),(3,16),(5,12),(5,13),(5,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2404_q : Finset ℕ := ([0,1,2,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2404_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(1,2),(1,3),(1,6),(1,7),(1,10),(1,13),(2,3),(2,6),(2,7),(2,10),(2,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_2405_q : Finset ℕ := ([0,1,2,3,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2405_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,14),(1,2),(1,3),(1,6),(1,7),(1,10),(1,14),(2,3),(2,6),(2,7),(2,10),(2,14),(3,6),(3,7),(3,10),(3,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2406_q : Finset ℕ := ([0,1,2,3,6,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2406_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,15),(1,2),(1,3),(1,6),(1,7),(1,10),(1,15),(2,3),(2,6),(2,7),(2,10),(2,15),(3,6),(3,7),(3,10),(3,15),(6,7),(6,10),(6,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2407_q : Finset ℕ := ([0,1,2,3,6,7,10,16] : List ℕ).toFinset
noncomputable def certificate_2407_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,7),(0,10),(0,16),(1,2),(1,3),(1,6),(1,7),(1,10),(1,16),(2,3),(2,6),(2,7),(2,10),(2,16),(3,6),(3,7),(3,10),(3,16),(6,7),(6,10),(6,16),(7,10),(7,16),(10,16)]

noncomputable def certificate_2408_q : Finset ℕ := ([0,1,2,3,6,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2408_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(0,15),(1,2),(1,3),(1,6),(1,7),(1,11),(1,15),(2,3),(2,6),(2,7),(2,11),(2,15),(3,6),(3,7),(3,11),(3,15),(6,7),(6,11),(6,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2409_q : Finset ℕ := ([0,1,2,3,6,7,11,16] : List ℕ).toFinset
noncomputable def certificate_2409_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,7),(0,11),(0,16),(1,2),(1,3),(1,6),(1,7),(1,11),(1,16),(2,3),(2,6),(2,7),(2,11),(2,16),(3,6),(3,7),(3,11),(3,16),(6,7),(6,11),(6,16),(7,11),(7,16),(11,16)]

noncomputable def certificate_2410_q : Finset ℕ := ([0,1,2,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2410_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(1,2),(1,3),(1,6),(1,8),(1,10),(1,13),(2,3),(2,6),(2,8),(2,10),(2,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2411_q : Finset ℕ := ([0,1,2,3,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2411_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,14),(1,2),(1,3),(1,6),(1,8),(1,10),(1,14),(2,3),(2,6),(2,8),(2,10),(2,14),(3,6),(3,8),(3,10),(3,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2412_q : Finset ℕ := ([0,1,2,3,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2412_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,15),(1,2),(1,3),(1,6),(1,8),(1,10),(1,15),(2,3),(2,6),(2,8),(2,10),(2,15),(3,6),(3,8),(3,10),(3,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2413_q : Finset ℕ := ([0,1,2,3,6,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2413_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,8),(0,10),(0,16),(1,2),(1,3),(1,6),(1,8),(1,10),(1,16),(2,3),(2,6),(2,8),(2,10),(2,16),(3,6),(3,8),(3,10),(3,16),(6,8),(6,10),(6,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2414_q : Finset ℕ := ([0,1,2,3,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2414_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(0,14),(1,2),(1,3),(1,6),(1,8),(1,11),(1,14),(2,3),(2,6),(2,8),(2,11),(2,14),(3,6),(3,8),(3,11),(3,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2415_q : Finset ℕ := ([0,1,2,3,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2415_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(0,15),(1,2),(1,3),(1,6),(1,8),(1,11),(1,15),(2,3),(2,6),(2,8),(2,11),(2,15),(3,6),(3,8),(3,11),(3,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2416_q : Finset ℕ := ([0,1,2,3,6,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2416_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,8),(0,11),(0,16),(1,2),(1,3),(1,6),(1,8),(1,11),(1,16),(2,3),(2,6),(2,8),(2,11),(2,16),(3,6),(3,8),(3,11),(3,16),(6,8),(6,11),(6,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2417_q : Finset ℕ := ([0,1,2,3,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2417_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(0,15),(1,2),(1,3),(1,6),(1,8),(1,12),(1,15),(2,3),(2,6),(2,8),(2,12),(2,15),(3,6),(3,8),(3,12),(3,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2418_q : Finset ℕ := ([0,1,2,3,6,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2418_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,8),(0,12),(0,16),(1,2),(1,3),(1,6),(1,8),(1,12),(1,16),(2,3),(2,6),(2,8),(2,12),(2,16),(3,6),(3,8),(3,12),(3,16),(6,8),(6,12),(6,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2419_q : Finset ℕ := ([0,1,2,3,6,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2419_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,8),(0,13),(0,16),(1,2),(1,3),(1,6),(1,8),(1,13),(1,16),(2,3),(2,6),(2,8),(2,13),(2,16),(3,6),(3,8),(3,13),(3,16),(6,8),(6,13),(6,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2420_q : Finset ℕ := ([0,1,2,3,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2420_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,3),(0,6),(0,9),(0,10),(0,14),(1,2),(1,3),(1,6),(1,9),(1,10),(1,14),(2,3),(2,6),(2,9),(2,10),(2,14),(3,6),(3,9),(3,10),(3,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2421_q : Finset ℕ := ([0,1,2,3,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2421_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,9),(0,10),(0,15),(1,2),(1,3),(1,6),(1,9),(1,10),(1,15),(2,3),(2,6),(2,9),(2,10),(2,15),(3,6),(3,9),(3,10),(3,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2422_q : Finset ℕ := ([0,1,2,3,6,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2422_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,9),(0,10),(0,16),(1,2),(1,3),(1,6),(1,9),(1,10),(1,16),(2,3),(2,6),(2,9),(2,10),(2,16),(3,6),(3,9),(3,10),(3,16),(6,9),(6,10),(6,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2423_q : Finset ℕ := ([0,1,2,3,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2423_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,9),(0,11),(0,15),(1,2),(1,3),(1,6),(1,9),(1,11),(1,15),(2,3),(2,6),(2,9),(2,11),(2,15),(3,6),(3,9),(3,11),(3,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2424_q : Finset ℕ := ([0,1,2,3,6,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2424_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,9),(0,11),(0,16),(1,2),(1,3),(1,6),(1,9),(1,11),(1,16),(2,3),(2,6),(2,9),(2,11),(2,16),(3,6),(3,9),(3,11),(3,16),(6,9),(6,11),(6,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2425_q : Finset ℕ := ([0,1,2,3,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2425_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,9),(0,12),(0,15),(1,2),(1,3),(1,6),(1,9),(1,12),(1,15),(2,3),(2,6),(2,9),(2,12),(2,15),(3,6),(3,9),(3,12),(3,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2426_q : Finset ℕ := ([0,1,2,3,6,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2426_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,9),(0,12),(0,16),(1,2),(1,3),(1,6),(1,9),(1,12),(1,16),(2,3),(2,6),(2,9),(2,12),(2,16),(3,6),(3,9),(3,12),(3,16),(6,9),(6,12),(6,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2427_q : Finset ℕ := ([0,1,2,3,6,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2427_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,9),(0,13),(0,16),(1,2),(1,3),(1,6),(1,9),(1,13),(1,16),(2,3),(2,6),(2,9),(2,13),(2,16),(3,6),(3,9),(3,13),(3,16),(6,9),(6,13),(6,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2428_q : Finset ℕ := ([0,1,2,3,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2428_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,6),(0,10),(0,11),(0,15),(1,2),(1,3),(1,6),(1,10),(1,11),(1,15),(2,3),(2,6),(2,10),(2,11),(2,15),(3,6),(3,10),(3,11),(3,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2429_q : Finset ℕ := ([0,1,2,3,6,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2429_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,10),(0,11),(0,16),(1,2),(1,3),(1,6),(1,10),(1,11),(1,16),(2,3),(2,6),(2,10),(2,11),(2,16),(3,6),(3,10),(3,11),(3,16),(6,10),(6,11),(6,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2430_q : Finset ℕ := ([0,1,2,3,6,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2430_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,10),(0,12),(0,16),(1,2),(1,3),(1,6),(1,10),(1,12),(1,16),(2,3),(2,6),(2,10),(2,12),(2,16),(3,6),(3,10),(3,12),(3,16),(6,10),(6,12),(6,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2431_q : Finset ℕ := ([0,1,2,3,6,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2431_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,6),(0,11),(0,12),(0,16),(1,2),(1,3),(1,6),(1,11),(1,12),(1,16),(2,3),(2,6),(2,11),(2,12),(2,16),(3,6),(3,11),(3,12),(3,16),(6,11),(6,12),(6,16),(11,12),(11,16),(12,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates077
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2432_q : Finset ℕ := ([0,1,2,3,7,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2432_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,7),(0,8),(0,12),(0,16),(1,2),(1,3),(1,7),(1,8),(1,12),(1,16),(2,3),(2,7),(2,8),(2,12),(2,16),(3,7),(3,8),(3,12),(3,16),(7,8),(7,12),(7,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2433_q : Finset ℕ := ([0,1,2,3,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2433_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,3),(0,7),(0,9),(0,11),(0,15),(1,2),(1,3),(1,7),(1,9),(1,11),(1,15),(2,3),(2,7),(2,9),(2,11),(2,15),(3,7),(3,9),(3,11),(3,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2434_q : Finset ℕ := ([0,1,2,3,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2434_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,7),(0,9),(0,11),(0,16),(1,2),(1,3),(1,7),(1,9),(1,11),(1,16),(2,3),(2,7),(2,9),(2,11),(2,16),(3,7),(3,9),(3,11),(3,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2435_q : Finset ℕ := ([0,1,2,3,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2435_edges : List (ℕ × ℕ) := [(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,3),(0,7),(0,9),(0,12),(0,16),(1,2),(1,3),(1,7),(1,9),(1,12),(1,16),(2,3),(2,7),(2,9),(2,12),(2,16),(3,7),(3,9),(3,12),(3,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2436_q : Finset ℕ := ([0,1,2,4,5,7,8,10] : List ℕ).toFinset
noncomputable def certificate_2436_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,10),(1,2),(1,4),(1,5),(1,7),(1,8),(1,10),(2,4),(2,5),(2,7),(2,8),(2,10),(4,5),(4,7),(4,8),(4,10),(5,7),(5,8),(5,10),(7,8),(7,10),(8,10)]

noncomputable def certificate_2437_q : Finset ℕ := ([0,1,2,4,5,7,8,11] : List ℕ).toFinset
noncomputable def certificate_2437_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,11),(1,2),(1,4),(1,5),(1,7),(1,8),(1,11),(2,4),(2,5),(2,7),(2,8),(2,11),(4,5),(4,7),(4,8),(4,11),(5,7),(5,8),(5,11),(7,8),(7,11),(8,11)]

noncomputable def certificate_2438_q : Finset ℕ := ([0,1,2,4,5,7,8,12] : List ℕ).toFinset
noncomputable def certificate_2438_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,12),(1,2),(1,4),(1,5),(1,7),(1,8),(1,12),(2,4),(2,5),(2,7),(2,8),(2,12),(4,5),(4,7),(4,8),(4,12),(5,7),(5,8),(5,12),(7,8),(7,12),(8,12)]

noncomputable def certificate_2439_q : Finset ℕ := ([0,1,2,4,5,7,8,13] : List ℕ).toFinset
noncomputable def certificate_2439_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,13),(1,2),(1,4),(1,5),(1,7),(1,8),(1,13),(2,4),(2,5),(2,7),(2,8),(2,13),(4,5),(4,7),(4,8),(4,13),(5,7),(5,8),(5,13),(7,8),(7,13),(8,13)]

noncomputable def certificate_2440_q : Finset ℕ := ([0,1,2,4,5,7,8,14] : List ℕ).toFinset
noncomputable def certificate_2440_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,14),(1,2),(1,4),(1,5),(1,7),(1,8),(1,14),(2,4),(2,5),(2,7),(2,8),(2,14),(4,5),(4,7),(4,8),(4,14),(5,7),(5,8),(5,14),(7,8),(7,14),(8,14)]

noncomputable def certificate_2441_q : Finset ℕ := ([0,1,2,4,5,7,8,15] : List ℕ).toFinset
noncomputable def certificate_2441_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,15),(1,2),(1,4),(1,5),(1,7),(1,8),(1,15),(2,4),(2,5),(2,7),(2,8),(2,15),(4,5),(4,7),(4,8),(4,15),(5,7),(5,8),(5,15),(7,8),(7,15),(8,15)]

noncomputable def certificate_2442_q : Finset ℕ := ([0,1,2,4,5,7,8,16] : List ℕ).toFinset
noncomputable def certificate_2442_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,8),(0,16),(1,2),(1,4),(1,5),(1,7),(1,8),(1,16),(2,4),(2,5),(2,7),(2,8),(2,16),(4,5),(4,7),(4,8),(4,16),(5,7),(5,8),(5,16),(7,8),(7,16),(8,16)]

noncomputable def certificate_2443_q : Finset ℕ := ([0,1,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_2443_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(1,2),(1,4),(1,5),(1,7),(1,9),(1,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_2444_q : Finset ℕ := ([0,1,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_2444_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(1,2),(1,4),(1,5),(1,7),(1,9),(1,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_2445_q : Finset ℕ := ([0,1,2,4,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_2445_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(1,2),(1,4),(1,5),(1,7),(1,9),(1,13),(2,4),(2,5),(2,7),(2,9),(2,13),(4,5),(4,7),(4,9),(4,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_2446_q : Finset ℕ := ([0,1,2,4,5,7,9,14] : List ℕ).toFinset
noncomputable def certificate_2446_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,14),(1,2),(1,4),(1,5),(1,7),(1,9),(1,14),(2,4),(2,5),(2,7),(2,9),(2,14),(4,5),(4,7),(4,9),(4,14),(5,7),(5,9),(5,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_2447_q : Finset ℕ := ([0,1,2,4,5,7,9,15] : List ℕ).toFinset
noncomputable def certificate_2447_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,15),(1,2),(1,4),(1,5),(1,7),(1,9),(1,15),(2,4),(2,5),(2,7),(2,9),(2,15),(4,5),(4,7),(4,9),(4,15),(5,7),(5,9),(5,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_2448_q : Finset ℕ := ([0,1,2,4,5,7,9,16] : List ℕ).toFinset
noncomputable def certificate_2448_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,9),(0,16),(1,2),(1,4),(1,5),(1,7),(1,9),(1,16),(2,4),(2,5),(2,7),(2,9),(2,16),(4,5),(4,7),(4,9),(4,16),(5,7),(5,9),(5,16),(7,9),(7,16),(9,16)]

noncomputable def certificate_2449_q : Finset ℕ := ([0,1,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_2449_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(1,2),(1,4),(1,5),(1,7),(1,10),(1,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_2450_q : Finset ℕ := ([0,1,2,4,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2450_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(1,2),(1,4),(1,5),(1,7),(1,10),(1,13),(2,4),(2,5),(2,7),(2,10),(2,13),(4,5),(4,7),(4,10),(4,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_2451_q : Finset ℕ := ([0,1,2,4,5,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2451_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,14),(1,2),(1,4),(1,5),(1,7),(1,10),(1,14),(2,4),(2,5),(2,7),(2,10),(2,14),(4,5),(4,7),(4,10),(4,14),(5,7),(5,10),(5,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2452_q : Finset ℕ := ([0,1,2,4,5,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2452_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,15),(1,2),(1,4),(1,5),(1,7),(1,10),(1,15),(2,4),(2,5),(2,7),(2,10),(2,15),(4,5),(4,7),(4,10),(4,15),(5,7),(5,10),(5,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2453_q : Finset ℕ := ([0,1,2,4,5,7,10,16] : List ℕ).toFinset
noncomputable def certificate_2453_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,10),(0,16),(1,2),(1,4),(1,5),(1,7),(1,10),(1,16),(2,4),(2,5),(2,7),(2,10),(2,16),(4,5),(4,7),(4,10),(4,16),(5,7),(5,10),(5,16),(7,10),(7,16),(10,16)]

noncomputable def certificate_2454_q : Finset ℕ := ([0,1,2,4,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_2454_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(1,2),(1,4),(1,5),(1,7),(1,11),(1,13),(2,4),(2,5),(2,7),(2,11),(2,13),(4,5),(4,7),(4,11),(4,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_2455_q : Finset ℕ := ([0,1,2,4,5,7,11,14] : List ℕ).toFinset
noncomputable def certificate_2455_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,14),(1,2),(1,4),(1,5),(1,7),(1,11),(1,14),(2,4),(2,5),(2,7),(2,11),(2,14),(4,5),(4,7),(4,11),(4,14),(5,7),(5,11),(5,14),(7,11),(7,14),(11,14)]

noncomputable def certificate_2456_q : Finset ℕ := ([0,1,2,4,5,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2456_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,15),(1,2),(1,4),(1,5),(1,7),(1,11),(1,15),(2,4),(2,5),(2,7),(2,11),(2,15),(4,5),(4,7),(4,11),(4,15),(5,7),(5,11),(5,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2457_q : Finset ℕ := ([0,1,2,4,5,7,11,16] : List ℕ).toFinset
noncomputable def certificate_2457_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,11),(0,16),(1,2),(1,4),(1,5),(1,7),(1,11),(1,16),(2,4),(2,5),(2,7),(2,11),(2,16),(4,5),(4,7),(4,11),(4,16),(5,7),(5,11),(5,16),(7,11),(7,16),(11,16)]

noncomputable def certificate_2458_q : Finset ℕ := ([0,1,2,4,5,7,12,14] : List ℕ).toFinset
noncomputable def certificate_2458_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(0,14),(1,2),(1,4),(1,5),(1,7),(1,12),(1,14),(2,4),(2,5),(2,7),(2,12),(2,14),(4,5),(4,7),(4,12),(4,14),(5,7),(5,12),(5,14),(7,12),(7,14),(12,14)]

noncomputable def certificate_2459_q : Finset ℕ := ([0,1,2,4,5,7,12,15] : List ℕ).toFinset
noncomputable def certificate_2459_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(0,15),(1,2),(1,4),(1,5),(1,7),(1,12),(1,15),(2,4),(2,5),(2,7),(2,12),(2,15),(4,5),(4,7),(4,12),(4,15),(5,7),(5,12),(5,15),(7,12),(7,15),(12,15)]

noncomputable def certificate_2460_q : Finset ℕ := ([0,1,2,4,5,7,12,16] : List ℕ).toFinset
noncomputable def certificate_2460_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,12),(0,16),(1,2),(1,4),(1,5),(1,7),(1,12),(1,16),(2,4),(2,5),(2,7),(2,12),(2,16),(4,5),(4,7),(4,12),(4,16),(5,7),(5,12),(5,16),(7,12),(7,16),(12,16)]

noncomputable def certificate_2461_q : Finset ℕ := ([0,1,2,4,5,7,13,15] : List ℕ).toFinset
noncomputable def certificate_2461_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,7),(0,13),(0,15),(1,2),(1,4),(1,5),(1,7),(1,13),(1,15),(2,4),(2,5),(2,7),(2,13),(2,15),(4,5),(4,7),(4,13),(4,15),(5,7),(5,13),(5,15),(7,13),(7,15),(13,15)]

noncomputable def certificate_2462_q : Finset ℕ := ([0,1,2,4,5,7,13,16] : List ℕ).toFinset
noncomputable def certificate_2462_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,13),(0,16),(1,2),(1,4),(1,5),(1,7),(1,13),(1,16),(2,4),(2,5),(2,7),(2,13),(2,16),(4,5),(4,7),(4,13),(4,16),(5,7),(5,13),(5,16),(7,13),(7,16),(13,16)]

noncomputable def certificate_2463_q : Finset ℕ := ([0,1,2,4,5,7,14,16] : List ℕ).toFinset
noncomputable def certificate_2463_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,7),(0,14),(0,16),(1,2),(1,4),(1,5),(1,7),(1,14),(1,16),(2,4),(2,5),(2,7),(2,14),(2,16),(4,5),(4,7),(4,14),(4,16),(5,7),(5,14),(5,16),(7,14),(7,16),(14,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates078
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2464_q : Finset ℕ := ([0,1,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2464_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(1,2),(1,4),(1,5),(1,8),(1,9),(1,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2465_q : Finset ℕ := ([0,1,2,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2465_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,13),(1,2),(1,4),(1,5),(1,8),(1,9),(1,13),(2,4),(2,5),(2,8),(2,9),(2,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2466_q : Finset ℕ := ([0,1,2,4,5,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2466_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,14),(1,2),(1,4),(1,5),(1,8),(1,9),(1,14),(2,4),(2,5),(2,8),(2,9),(2,14),(4,5),(4,8),(4,9),(4,14),(5,8),(5,9),(5,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2467_q : Finset ℕ := ([0,1,2,4,5,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2467_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,15),(1,2),(1,4),(1,5),(1,8),(1,9),(1,15),(2,4),(2,5),(2,8),(2,9),(2,15),(4,5),(4,8),(4,9),(4,15),(5,8),(5,9),(5,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2468_q : Finset ℕ := ([0,1,2,4,5,8,9,16] : List ℕ).toFinset
noncomputable def certificate_2468_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,8),(0,9),(0,16),(1,2),(1,4),(1,5),(1,8),(1,9),(1,16),(2,4),(2,5),(2,8),(2,9),(2,16),(4,5),(4,8),(4,9),(4,16),(5,8),(5,9),(5,16),(8,9),(8,16),(9,16)]

noncomputable def certificate_2469_q : Finset ℕ := ([0,1,2,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2469_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(1,2),(1,4),(1,5),(1,8),(1,10),(1,13),(2,4),(2,5),(2,8),(2,10),(2,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2470_q : Finset ℕ := ([0,1,2,4,5,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2470_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,14),(1,2),(1,4),(1,5),(1,8),(1,10),(1,14),(2,4),(2,5),(2,8),(2,10),(2,14),(4,5),(4,8),(4,10),(4,14),(5,8),(5,10),(5,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2471_q : Finset ℕ := ([0,1,2,4,5,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2471_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,15),(1,2),(1,4),(1,5),(1,8),(1,10),(1,15),(2,4),(2,5),(2,8),(2,10),(2,15),(4,5),(4,8),(4,10),(4,15),(5,8),(5,10),(5,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2472_q : Finset ℕ := ([0,1,2,4,5,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2472_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,8),(0,10),(0,16),(1,2),(1,4),(1,5),(1,8),(1,10),(1,16),(2,4),(2,5),(2,8),(2,10),(2,16),(4,5),(4,8),(4,10),(4,16),(5,8),(5,10),(5,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2473_q : Finset ℕ := ([0,1,2,4,5,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2473_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(0,14),(1,2),(1,4),(1,5),(1,8),(1,11),(1,14),(2,4),(2,5),(2,8),(2,11),(2,14),(4,5),(4,8),(4,11),(4,14),(5,8),(5,11),(5,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2474_q : Finset ℕ := ([0,1,2,4,5,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2474_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(0,15),(1,2),(1,4),(1,5),(1,8),(1,11),(1,15),(2,4),(2,5),(2,8),(2,11),(2,15),(4,5),(4,8),(4,11),(4,15),(5,8),(5,11),(5,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2475_q : Finset ℕ := ([0,1,2,4,5,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2475_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,8),(0,11),(0,16),(1,2),(1,4),(1,5),(1,8),(1,11),(1,16),(2,4),(2,5),(2,8),(2,11),(2,16),(4,5),(4,8),(4,11),(4,16),(5,8),(5,11),(5,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2476_q : Finset ℕ := ([0,1,2,4,5,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2476_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,8),(0,12),(0,15),(1,2),(1,4),(1,5),(1,8),(1,12),(1,15),(2,4),(2,5),(2,8),(2,12),(2,15),(4,5),(4,8),(4,12),(4,15),(5,8),(5,12),(5,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2477_q : Finset ℕ := ([0,1,2,4,5,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2477_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,8),(0,12),(0,16),(1,2),(1,4),(1,5),(1,8),(1,12),(1,16),(2,4),(2,5),(2,8),(2,12),(2,16),(4,5),(4,8),(4,12),(4,16),(5,8),(5,12),(5,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2478_q : Finset ℕ := ([0,1,2,4,5,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2478_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,8),(0,13),(0,16),(1,2),(1,4),(1,5),(1,8),(1,13),(1,16),(2,4),(2,5),(2,8),(2,13),(2,16),(4,5),(4,8),(4,13),(4,16),(5,8),(5,13),(5,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2479_q : Finset ℕ := ([0,1,2,4,5,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2479_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,5),(0,9),(0,10),(0,14),(1,2),(1,4),(1,5),(1,9),(1,10),(1,14),(2,4),(2,5),(2,9),(2,10),(2,14),(4,5),(4,9),(4,10),(4,14),(5,9),(5,10),(5,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2480_q : Finset ℕ := ([0,1,2,4,5,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2480_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,9),(0,10),(0,15),(1,2),(1,4),(1,5),(1,9),(1,10),(1,15),(2,4),(2,5),(2,9),(2,10),(2,15),(4,5),(4,9),(4,10),(4,15),(5,9),(5,10),(5,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2481_q : Finset ℕ := ([0,1,2,4,5,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2481_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,9),(0,10),(0,16),(1,2),(1,4),(1,5),(1,9),(1,10),(1,16),(2,4),(2,5),(2,9),(2,10),(2,16),(4,5),(4,9),(4,10),(4,16),(5,9),(5,10),(5,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2482_q : Finset ℕ := ([0,1,2,4,5,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2482_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,5),(0,9),(0,11),(0,15),(1,2),(1,4),(1,5),(1,9),(1,11),(1,15),(2,4),(2,5),(2,9),(2,11),(2,15),(4,5),(4,9),(4,11),(4,15),(5,9),(5,11),(5,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2483_q : Finset ℕ := ([0,1,2,4,5,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2483_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,9),(0,11),(0,16),(1,2),(1,4),(1,5),(1,9),(1,11),(1,16),(2,4),(2,5),(2,9),(2,11),(2,16),(4,5),(4,9),(4,11),(4,16),(5,9),(5,11),(5,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2484_q : Finset ℕ := ([0,1,2,4,5,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2484_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,9),(0,12),(0,16),(1,2),(1,4),(1,5),(1,9),(1,12),(1,16),(2,4),(2,5),(2,9),(2,12),(2,16),(4,5),(4,9),(4,12),(4,16),(5,9),(5,12),(5,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2485_q : Finset ℕ := ([0,1,2,4,5,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2485_edges : List (ℕ × ℕ) := [(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,5),(0,10),(0,11),(0,16),(1,2),(1,4),(1,5),(1,10),(1,11),(1,16),(2,4),(2,5),(2,10),(2,11),(2,16),(4,5),(4,10),(4,11),(4,16),(5,10),(5,11),(5,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2486_q : Finset ℕ := ([0,1,2,4,6,7,9,11] : List ℕ).toFinset
noncomputable def certificate_2486_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,11),(1,2),(1,4),(1,6),(1,7),(1,9),(1,11),(2,4),(2,6),(2,7),(2,9),(2,11),(4,6),(4,7),(4,9),(4,11),(6,7),(6,9),(6,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_2487_q : Finset ℕ := ([0,1,2,4,6,7,9,12] : List ℕ).toFinset
noncomputable def certificate_2487_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,12),(1,2),(1,4),(1,6),(1,7),(1,9),(1,12),(2,4),(2,6),(2,7),(2,9),(2,12),(4,6),(4,7),(4,9),(4,12),(6,7),(6,9),(6,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_2488_q : Finset ℕ := ([0,1,2,4,6,7,9,13] : List ℕ).toFinset
noncomputable def certificate_2488_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,13),(1,2),(1,4),(1,6),(1,7),(1,9),(1,13),(2,4),(2,6),(2,7),(2,9),(2,13),(4,6),(4,7),(4,9),(4,13),(6,7),(6,9),(6,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_2489_q : Finset ℕ := ([0,1,2,4,6,7,9,14] : List ℕ).toFinset
noncomputable def certificate_2489_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,14),(1,2),(1,4),(1,6),(1,7),(1,9),(1,14),(2,4),(2,6),(2,7),(2,9),(2,14),(4,6),(4,7),(4,9),(4,14),(6,7),(6,9),(6,14),(7,9),(7,14),(9,14)]

noncomputable def certificate_2490_q : Finset ℕ := ([0,1,2,4,6,7,9,15] : List ℕ).toFinset
noncomputable def certificate_2490_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,15),(1,2),(1,4),(1,6),(1,7),(1,9),(1,15),(2,4),(2,6),(2,7),(2,9),(2,15),(4,6),(4,7),(4,9),(4,15),(6,7),(6,9),(6,15),(7,9),(7,15),(9,15)]

noncomputable def certificate_2491_q : Finset ℕ := ([0,1,2,4,6,7,9,16] : List ℕ).toFinset
noncomputable def certificate_2491_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,7),(0,9),(0,16),(1,2),(1,4),(1,6),(1,7),(1,9),(1,16),(2,4),(2,6),(2,7),(2,9),(2,16),(4,6),(4,7),(4,9),(4,16),(6,7),(6,9),(6,16),(7,9),(7,16),(9,16)]

noncomputable def certificate_2492_q : Finset ℕ := ([0,1,2,4,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_2492_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,13),(1,2),(1,4),(1,6),(1,7),(1,10),(1,13),(2,4),(2,6),(2,7),(2,10),(2,13),(4,6),(4,7),(4,10),(4,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_2493_q : Finset ℕ := ([0,1,2,4,6,7,10,14] : List ℕ).toFinset
noncomputable def certificate_2493_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,14),(1,2),(1,4),(1,6),(1,7),(1,10),(1,14),(2,4),(2,6),(2,7),(2,10),(2,14),(4,6),(4,7),(4,10),(4,14),(6,7),(6,10),(6,14),(7,10),(7,14),(10,14)]

noncomputable def certificate_2494_q : Finset ℕ := ([0,1,2,4,6,7,10,15] : List ℕ).toFinset
noncomputable def certificate_2494_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,15),(1,2),(1,4),(1,6),(1,7),(1,10),(1,15),(2,4),(2,6),(2,7),(2,10),(2,15),(4,6),(4,7),(4,10),(4,15),(6,7),(6,10),(6,15),(7,10),(7,15),(10,15)]

noncomputable def certificate_2495_q : Finset ℕ := ([0,1,2,4,6,7,10,16] : List ℕ).toFinset
noncomputable def certificate_2495_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,7),(0,10),(0,16),(1,2),(1,4),(1,6),(1,7),(1,10),(1,16),(2,4),(2,6),(2,7),(2,10),(2,16),(4,6),(4,7),(4,10),(4,16),(6,7),(6,10),(6,16),(7,10),(7,16),(10,16)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates079
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2496_q : Finset ℕ := ([0,1,2,4,6,7,11,15] : List ℕ).toFinset
noncomputable def certificate_2496_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(0,15),(1,2),(1,4),(1,6),(1,7),(1,11),(1,15),(2,4),(2,6),(2,7),(2,11),(2,15),(4,6),(4,7),(4,11),(4,15),(6,7),(6,11),(6,15),(7,11),(7,15),(11,15)]

noncomputable def certificate_2497_q : Finset ℕ := ([0,1,2,4,6,7,11,16] : List ℕ).toFinset
noncomputable def certificate_2497_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,7),(0,11),(0,16),(1,2),(1,4),(1,6),(1,7),(1,11),(1,16),(2,4),(2,6),(2,7),(2,11),(2,16),(4,6),(4,7),(4,11),(4,16),(6,7),(6,11),(6,16),(7,11),(7,16),(11,16)]

noncomputable def certificate_2498_q : Finset ℕ := ([0,1,2,4,6,8,9,12] : List ℕ).toFinset
noncomputable def certificate_2498_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,12),(1,2),(1,4),(1,6),(1,8),(1,9),(1,12),(2,4),(2,6),(2,8),(2,9),(2,12),(4,6),(4,8),(4,9),(4,12),(6,8),(6,9),(6,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_2499_q : Finset ℕ := ([0,1,2,4,6,8,9,13] : List ℕ).toFinset
noncomputable def certificate_2499_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,13),(1,2),(1,4),(1,6),(1,8),(1,9),(1,13),(2,4),(2,6),(2,8),(2,9),(2,13),(4,6),(4,8),(4,9),(4,13),(6,8),(6,9),(6,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_2500_q : Finset ℕ := ([0,1,2,4,6,8,9,14] : List ℕ).toFinset
noncomputable def certificate_2500_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,14),(1,2),(1,4),(1,6),(1,8),(1,9),(1,14),(2,4),(2,6),(2,8),(2,9),(2,14),(4,6),(4,8),(4,9),(4,14),(6,8),(6,9),(6,14),(8,9),(8,14),(9,14)]

noncomputable def certificate_2501_q : Finset ℕ := ([0,1,2,4,6,8,9,15] : List ℕ).toFinset
noncomputable def certificate_2501_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,15),(1,2),(1,4),(1,6),(1,8),(1,9),(1,15),(2,4),(2,6),(2,8),(2,9),(2,15),(4,6),(4,8),(4,9),(4,15),(6,8),(6,9),(6,15),(8,9),(8,15),(9,15)]

noncomputable def certificate_2502_q : Finset ℕ := ([0,1,2,4,6,8,9,16] : List ℕ).toFinset
noncomputable def certificate_2502_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,8),(0,9),(0,16),(1,2),(1,4),(1,6),(1,8),(1,9),(1,16),(2,4),(2,6),(2,8),(2,9),(2,16),(4,6),(4,8),(4,9),(4,16),(6,8),(6,9),(6,16),(8,9),(8,16),(9,16)]

noncomputable def certificate_2503_q : Finset ℕ := ([0,1,2,4,6,8,10,12] : List ℕ).toFinset
noncomputable def certificate_2503_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,12),(1,2),(1,4),(1,6),(1,8),(1,10),(1,12),(2,4),(2,6),(2,8),(2,10),(2,12),(4,6),(4,8),(4,10),(4,12),(6,8),(6,10),(6,12),(8,10),(8,12),(10,12)]

noncomputable def certificate_2504_q : Finset ℕ := ([0,1,2,4,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2504_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,13),(1,2),(1,4),(1,6),(1,8),(1,10),(1,13),(2,4),(2,6),(2,8),(2,10),(2,13),(4,6),(4,8),(4,10),(4,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2505_q : Finset ℕ := ([0,1,2,4,6,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2505_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,14),(1,2),(1,4),(1,6),(1,8),(1,10),(1,14),(2,4),(2,6),(2,8),(2,10),(2,14),(4,6),(4,8),(4,10),(4,14),(6,8),(6,10),(6,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2506_q : Finset ℕ := ([0,1,2,4,6,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2506_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,15),(1,2),(1,4),(1,6),(1,8),(1,10),(1,15),(2,4),(2,6),(2,8),(2,10),(2,15),(4,6),(4,8),(4,10),(4,15),(6,8),(6,10),(6,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2507_q : Finset ℕ := ([0,1,2,4,6,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2507_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,8),(0,10),(0,16),(1,2),(1,4),(1,6),(1,8),(1,10),(1,16),(2,4),(2,6),(2,8),(2,10),(2,16),(4,6),(4,8),(4,10),(4,16),(6,8),(6,10),(6,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2508_q : Finset ℕ := ([0,1,2,4,6,8,11,13] : List ℕ).toFinset
noncomputable def certificate_2508_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,13),(1,2),(1,4),(1,6),(1,8),(1,11),(1,13),(2,4),(2,6),(2,8),(2,11),(2,13),(4,6),(4,8),(4,11),(4,13),(6,8),(6,11),(6,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_2509_q : Finset ℕ := ([0,1,2,4,6,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2509_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,14),(1,2),(1,4),(1,6),(1,8),(1,11),(1,14),(2,4),(2,6),(2,8),(2,11),(2,14),(4,6),(4,8),(4,11),(4,14),(6,8),(6,11),(6,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2510_q : Finset ℕ := ([0,1,2,4,6,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2510_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,15),(1,2),(1,4),(1,6),(1,8),(1,11),(1,15),(2,4),(2,6),(2,8),(2,11),(2,15),(4,6),(4,8),(4,11),(4,15),(6,8),(6,11),(6,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2511_q : Finset ℕ := ([0,1,2,4,6,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2511_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,8),(0,11),(0,16),(1,2),(1,4),(1,6),(1,8),(1,11),(1,16),(2,4),(2,6),(2,8),(2,11),(2,16),(4,6),(4,8),(4,11),(4,16),(6,8),(6,11),(6,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2512_q : Finset ℕ := ([0,1,2,4,6,8,12,14] : List ℕ).toFinset
noncomputable def certificate_2512_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(0,14),(1,2),(1,4),(1,6),(1,8),(1,12),(1,14),(2,4),(2,6),(2,8),(2,12),(2,14),(4,6),(4,8),(4,12),(4,14),(6,8),(6,12),(6,14),(8,12),(8,14),(12,14)]

noncomputable def certificate_2513_q : Finset ℕ := ([0,1,2,4,6,8,12,15] : List ℕ).toFinset
noncomputable def certificate_2513_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(0,15),(1,2),(1,4),(1,6),(1,8),(1,12),(1,15),(2,4),(2,6),(2,8),(2,12),(2,15),(4,6),(4,8),(4,12),(4,15),(6,8),(6,12),(6,15),(8,12),(8,15),(12,15)]

noncomputable def certificate_2514_q : Finset ℕ := ([0,1,2,4,6,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2514_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,8),(0,12),(0,16),(1,2),(1,4),(1,6),(1,8),(1,12),(1,16),(2,4),(2,6),(2,8),(2,12),(2,16),(4,6),(4,8),(4,12),(4,16),(6,8),(6,12),(6,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2515_q : Finset ℕ := ([0,1,2,4,6,8,13,15] : List ℕ).toFinset
noncomputable def certificate_2515_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,8),(0,13),(0,15),(1,2),(1,4),(1,6),(1,8),(1,13),(1,15),(2,4),(2,6),(2,8),(2,13),(2,15),(4,6),(4,8),(4,13),(4,15),(6,8),(6,13),(6,15),(8,13),(8,15),(13,15)]

noncomputable def certificate_2516_q : Finset ℕ := ([0,1,2,4,6,8,13,16] : List ℕ).toFinset
noncomputable def certificate_2516_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,8),(0,13),(0,16),(1,2),(1,4),(1,6),(1,8),(1,13),(1,16),(2,4),(2,6),(2,8),(2,13),(2,16),(4,6),(4,8),(4,13),(4,16),(6,8),(6,13),(6,16),(8,13),(8,16),(13,16)]

noncomputable def certificate_2517_q : Finset ℕ := ([0,1,2,4,6,8,14,16] : List ℕ).toFinset
noncomputable def certificate_2517_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,8),(0,14),(0,16),(1,2),(1,4),(1,6),(1,8),(1,14),(1,16),(2,4),(2,6),(2,8),(2,14),(2,16),(4,6),(4,8),(4,14),(4,16),(6,8),(6,14),(6,16),(8,14),(8,16),(14,16)]

noncomputable def certificate_2518_q : Finset ℕ := ([0,1,2,4,6,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2518_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,13),(1,2),(1,4),(1,6),(1,9),(1,10),(1,13),(2,4),(2,6),(2,9),(2,10),(2,13),(4,6),(4,9),(4,10),(4,13),(6,9),(6,10),(6,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2519_q : Finset ℕ := ([0,1,2,4,6,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2519_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,14),(1,2),(1,4),(1,6),(1,9),(1,10),(1,14),(2,4),(2,6),(2,9),(2,10),(2,14),(4,6),(4,9),(4,10),(4,14),(6,9),(6,10),(6,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2520_q : Finset ℕ := ([0,1,2,4,6,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2520_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,15),(1,2),(1,4),(1,6),(1,9),(1,10),(1,15),(2,4),(2,6),(2,9),(2,10),(2,15),(4,6),(4,9),(4,10),(4,15),(6,9),(6,10),(6,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2521_q : Finset ℕ := ([0,1,2,4,6,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2521_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,9),(0,10),(0,16),(1,2),(1,4),(1,6),(1,9),(1,10),(1,16),(2,4),(2,6),(2,9),(2,10),(2,16),(4,6),(4,9),(4,10),(4,16),(6,9),(6,10),(6,16),(9,10),(9,16),(10,16)]

noncomputable def certificate_2522_q : Finset ℕ := ([0,1,2,4,6,9,11,13] : List ℕ).toFinset
noncomputable def certificate_2522_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,13),(1,2),(1,4),(1,6),(1,9),(1,11),(1,13),(2,4),(2,6),(2,9),(2,11),(2,13),(4,6),(4,9),(4,11),(4,13),(6,9),(6,11),(6,13),(9,11),(9,13),(11,13)]

noncomputable def certificate_2523_q : Finset ℕ := ([0,1,2,4,6,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2523_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,14),(1,2),(1,4),(1,6),(1,9),(1,11),(1,14),(2,4),(2,6),(2,9),(2,11),(2,14),(4,6),(4,9),(4,11),(4,14),(6,9),(6,11),(6,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2524_q : Finset ℕ := ([0,1,2,4,6,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2524_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,15),(1,2),(1,4),(1,6),(1,9),(1,11),(1,15),(2,4),(2,6),(2,9),(2,11),(2,15),(4,6),(4,9),(4,11),(4,15),(6,9),(6,11),(6,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2525_q : Finset ℕ := ([0,1,2,4,6,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2525_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,9),(0,11),(0,16),(1,2),(1,4),(1,6),(1,9),(1,11),(1,16),(2,4),(2,6),(2,9),(2,11),(2,16),(4,6),(4,9),(4,11),(4,16),(6,9),(6,11),(6,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2526_q : Finset ℕ := ([0,1,2,4,6,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2526_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(0,14),(1,2),(1,4),(1,6),(1,9),(1,12),(1,14),(2,4),(2,6),(2,9),(2,12),(2,14),(4,6),(4,9),(4,12),(4,14),(6,9),(6,12),(6,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2527_q : Finset ℕ := ([0,1,2,4,6,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2527_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(0,15),(1,2),(1,4),(1,6),(1,9),(1,12),(1,15),(2,4),(2,6),(2,9),(2,12),(2,15),(4,6),(4,9),(4,12),(4,15),(6,9),(6,12),(6,15),(9,12),(9,15),(12,15)]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates080
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_2528_q : Finset ℕ := ([0,1,2,4,6,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2528_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,9),(0,12),(0,16),(1,2),(1,4),(1,6),(1,9),(1,12),(1,16),(2,4),(2,6),(2,9),(2,12),(2,16),(4,6),(4,9),(4,12),(4,16),(6,9),(6,12),(6,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2529_q : Finset ℕ := ([0,1,2,4,6,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2529_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,9),(0,13),(0,15),(1,2),(1,4),(1,6),(1,9),(1,13),(1,15),(2,4),(2,6),(2,9),(2,13),(2,15),(4,6),(4,9),(4,13),(4,15),(6,9),(6,13),(6,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2530_q : Finset ℕ := ([0,1,2,4,6,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2530_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,9),(0,13),(0,16),(1,2),(1,4),(1,6),(1,9),(1,13),(1,16),(2,4),(2,6),(2,9),(2,13),(2,16),(4,6),(4,9),(4,13),(4,16),(6,9),(6,13),(6,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2531_q : Finset ℕ := ([0,1,2,4,6,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2531_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,9),(0,14),(0,16),(1,2),(1,4),(1,6),(1,9),(1,14),(1,16),(2,4),(2,6),(2,9),(2,14),(2,16),(4,6),(4,9),(4,14),(4,16),(6,9),(6,14),(6,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2532_q : Finset ℕ := ([0,1,2,4,6,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2532_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,14),(1,2),(1,4),(1,6),(1,10),(1,11),(1,14),(2,4),(2,6),(2,10),(2,11),(2,14),(4,6),(4,10),(4,11),(4,14),(6,10),(6,11),(6,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2533_q : Finset ℕ := ([0,1,2,4,6,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2533_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,15),(1,2),(1,4),(1,6),(1,10),(1,11),(1,15),(2,4),(2,6),(2,10),(2,11),(2,15),(4,6),(4,10),(4,11),(4,15),(6,10),(6,11),(6,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2534_q : Finset ℕ := ([0,1,2,4,6,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2534_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,10),(0,11),(0,16),(1,2),(1,4),(1,6),(1,10),(1,11),(1,16),(2,4),(2,6),(2,10),(2,11),(2,16),(4,6),(4,10),(4,11),(4,16),(6,10),(6,11),(6,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2535_q : Finset ℕ := ([0,1,2,4,6,10,12,14] : List ℕ).toFinset
noncomputable def certificate_2535_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(0,14),(1,2),(1,4),(1,6),(1,10),(1,12),(1,14),(2,4),(2,6),(2,10),(2,12),(2,14),(4,6),(4,10),(4,12),(4,14),(6,10),(6,12),(6,14),(10,12),(10,14),(12,14)]

noncomputable def certificate_2536_q : Finset ℕ := ([0,1,2,4,6,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2536_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(0,15),(1,2),(1,4),(1,6),(1,10),(1,12),(1,15),(2,4),(2,6),(2,10),(2,12),(2,15),(4,6),(4,10),(4,12),(4,15),(6,10),(6,12),(6,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2537_q : Finset ℕ := ([0,1,2,4,6,10,12,16] : List ℕ).toFinset
noncomputable def certificate_2537_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,10),(0,12),(0,16),(1,2),(1,4),(1,6),(1,10),(1,12),(1,16),(2,4),(2,6),(2,10),(2,12),(2,16),(4,6),(4,10),(4,12),(4,16),(6,10),(6,12),(6,16),(10,12),(10,16),(12,16)]

noncomputable def certificate_2538_q : Finset ℕ := ([0,1,2,4,6,10,13,15] : List ℕ).toFinset
noncomputable def certificate_2538_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,10),(0,13),(0,15),(1,2),(1,4),(1,6),(1,10),(1,13),(1,15),(2,4),(2,6),(2,10),(2,13),(2,15),(4,6),(4,10),(4,13),(4,15),(6,10),(6,13),(6,15),(10,13),(10,15),(13,15)]

noncomputable def certificate_2539_q : Finset ℕ := ([0,1,2,4,6,10,13,16] : List ℕ).toFinset
noncomputable def certificate_2539_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,10),(0,13),(0,16),(1,2),(1,4),(1,6),(1,10),(1,13),(1,16),(2,4),(2,6),(2,10),(2,13),(2,16),(4,6),(4,10),(4,13),(4,16),(6,10),(6,13),(6,16),(10,13),(10,16),(13,16)]

noncomputable def certificate_2540_q : Finset ℕ := ([0,1,2,4,6,10,14,16] : List ℕ).toFinset
noncomputable def certificate_2540_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,10),(0,14),(0,16),(1,2),(1,4),(1,6),(1,10),(1,14),(1,16),(2,4),(2,6),(2,10),(2,14),(2,16),(4,6),(4,10),(4,14),(4,16),(6,10),(6,14),(6,16),(10,14),(10,16),(14,16)]

noncomputable def certificate_2541_q : Finset ℕ := ([0,1,2,4,6,11,12,15] : List ℕ).toFinset
noncomputable def certificate_2541_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,11),(0,12),(0,15),(1,2),(1,4),(1,6),(1,11),(1,12),(1,15),(2,4),(2,6),(2,11),(2,12),(2,15),(4,6),(4,11),(4,12),(4,15),(6,11),(6,12),(6,15),(11,12),(11,15),(12,15)]

noncomputable def certificate_2542_q : Finset ℕ := ([0,1,2,4,6,11,12,16] : List ℕ).toFinset
noncomputable def certificate_2542_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,11),(0,12),(0,16),(1,2),(1,4),(1,6),(1,11),(1,12),(1,16),(2,4),(2,6),(2,11),(2,12),(2,16),(4,6),(4,11),(4,12),(4,16),(6,11),(6,12),(6,16),(11,12),(11,16),(12,16)]

noncomputable def certificate_2543_q : Finset ℕ := ([0,1,2,4,6,11,13,15] : List ℕ).toFinset
noncomputable def certificate_2543_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,6),(0,11),(0,13),(0,15),(1,2),(1,4),(1,6),(1,11),(1,13),(1,15),(2,4),(2,6),(2,11),(2,13),(2,15),(4,6),(4,11),(4,13),(4,15),(6,11),(6,13),(6,15),(11,13),(11,15),(13,15)]

noncomputable def certificate_2544_q : Finset ℕ := ([0,1,2,4,6,11,13,16] : List ℕ).toFinset
noncomputable def certificate_2544_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,11),(0,13),(0,16),(1,2),(1,4),(1,6),(1,11),(1,13),(1,16),(2,4),(2,6),(2,11),(2,13),(2,16),(4,6),(4,11),(4,13),(4,16),(6,11),(6,13),(6,16),(11,13),(11,16),(13,16)]

noncomputable def certificate_2545_q : Finset ℕ := ([0,1,2,4,6,11,14,16] : List ℕ).toFinset
noncomputable def certificate_2545_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,11),(0,14),(0,16),(1,2),(1,4),(1,6),(1,11),(1,14),(1,16),(2,4),(2,6),(2,11),(2,14),(2,16),(4,6),(4,11),(4,14),(4,16),(6,11),(6,14),(6,16),(11,14),(11,16),(14,16)]

noncomputable def certificate_2546_q : Finset ℕ := ([0,1,2,4,6,12,13,16] : List ℕ).toFinset
noncomputable def certificate_2546_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,12),(0,13),(0,16),(1,2),(1,4),(1,6),(1,12),(1,13),(1,16),(2,4),(2,6),(2,12),(2,13),(2,16),(4,6),(4,12),(4,13),(4,16),(6,12),(6,13),(6,16),(12,13),(12,16),(13,16)]

noncomputable def certificate_2547_q : Finset ℕ := ([0,1,2,4,6,12,14,16] : List ℕ).toFinset
noncomputable def certificate_2547_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,6),(0,12),(0,14),(0,16),(1,2),(1,4),(1,6),(1,12),(1,14),(1,16),(2,4),(2,6),(2,12),(2,14),(2,16),(4,6),(4,12),(4,14),(4,16),(6,12),(6,14),(6,16),(12,14),(12,16),(14,16)]

noncomputable def certificate_2548_q : Finset ℕ := ([0,1,2,4,7,8,10,13] : List ℕ).toFinset
noncomputable def certificate_2548_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,13),(1,2),(1,4),(1,7),(1,8),(1,10),(1,13),(2,4),(2,7),(2,8),(2,10),(2,13),(4,7),(4,8),(4,10),(4,13),(7,8),(7,10),(7,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_2549_q : Finset ℕ := ([0,1,2,4,7,8,10,14] : List ℕ).toFinset
noncomputable def certificate_2549_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,14),(1,2),(1,4),(1,7),(1,8),(1,10),(1,14),(2,4),(2,7),(2,8),(2,10),(2,14),(4,7),(4,8),(4,10),(4,14),(7,8),(7,10),(7,14),(8,10),(8,14),(10,14)]

noncomputable def certificate_2550_q : Finset ℕ := ([0,1,2,4,7,8,10,15] : List ℕ).toFinset
noncomputable def certificate_2550_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,15),(1,2),(1,4),(1,7),(1,8),(1,10),(1,15),(2,4),(2,7),(2,8),(2,10),(2,15),(4,7),(4,8),(4,10),(4,15),(7,8),(7,10),(7,15),(8,10),(8,15),(10,15)]

noncomputable def certificate_2551_q : Finset ℕ := ([0,1,2,4,7,8,10,16] : List ℕ).toFinset
noncomputable def certificate_2551_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,8),(0,10),(0,16),(1,2),(1,4),(1,7),(1,8),(1,10),(1,16),(2,4),(2,7),(2,8),(2,10),(2,16),(4,7),(4,8),(4,10),(4,16),(7,8),(7,10),(7,16),(8,10),(8,16),(10,16)]

noncomputable def certificate_2552_q : Finset ℕ := ([0,1,2,4,7,8,11,14] : List ℕ).toFinset
noncomputable def certificate_2552_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(0,14),(1,2),(1,4),(1,7),(1,8),(1,11),(1,14),(2,4),(2,7),(2,8),(2,11),(2,14),(4,7),(4,8),(4,11),(4,14),(7,8),(7,11),(7,14),(8,11),(8,14),(11,14)]

noncomputable def certificate_2553_q : Finset ℕ := ([0,1,2,4,7,8,11,15] : List ℕ).toFinset
noncomputable def certificate_2553_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(0,15),(1,2),(1,4),(1,7),(1,8),(1,11),(1,15),(2,4),(2,7),(2,8),(2,11),(2,15),(4,7),(4,8),(4,11),(4,15),(7,8),(7,11),(7,15),(8,11),(8,15),(11,15)]

noncomputable def certificate_2554_q : Finset ℕ := ([0,1,2,4,7,8,11,16] : List ℕ).toFinset
noncomputable def certificate_2554_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,8),(0,11),(0,16),(1,2),(1,4),(1,7),(1,8),(1,11),(1,16),(2,4),(2,7),(2,8),(2,11),(2,16),(4,7),(4,8),(4,11),(4,16),(7,8),(7,11),(7,16),(8,11),(8,16),(11,16)]

noncomputable def certificate_2555_q : Finset ℕ := ([0,1,2,4,7,8,12,16] : List ℕ).toFinset
noncomputable def certificate_2555_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,8),(0,12),(0,16),(1,2),(1,4),(1,7),(1,8),(1,12),(1,16),(2,4),(2,7),(2,8),(2,12),(2,16),(4,7),(4,8),(4,12),(4,16),(7,8),(7,12),(7,16),(8,12),(8,16),(12,16)]

noncomputable def certificate_2556_q : Finset ℕ := ([0,1,2,4,7,9,10,13] : List ℕ).toFinset
noncomputable def certificate_2556_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,13),(1,2),(1,4),(1,7),(1,9),(1,10),(1,13),(2,4),(2,7),(2,9),(2,10),(2,13),(4,7),(4,9),(4,10),(4,13),(7,9),(7,10),(7,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_2557_q : Finset ℕ := ([0,1,2,4,7,9,10,14] : List ℕ).toFinset
noncomputable def certificate_2557_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,14),(1,2),(1,4),(1,7),(1,9),(1,10),(1,14),(2,4),(2,7),(2,9),(2,10),(2,14),(4,7),(4,9),(4,10),(4,14),(7,9),(7,10),(7,14),(9,10),(9,14),(10,14)]

noncomputable def certificate_2558_q : Finset ℕ := ([0,1,2,4,7,9,10,15] : List ℕ).toFinset
noncomputable def certificate_2558_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,15),(1,2),(1,4),(1,7),(1,9),(1,10),(1,15),(2,4),(2,7),(2,9),(2,10),(2,15),(4,7),(4,9),(4,10),(4,15),(7,9),(7,10),(7,15),(9,10),(9,15),(10,15)]

noncomputable def certificate_2559_q : Finset ℕ := ([0,1,2,4,7,9,10,16] : List ℕ).toFinset
noncomputable def certificate_2559_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,9),(0,10),(0,16),(1,2),(1,4),(1,7),(1,9),(1,10),(1,16),(2,4),(2,7),(2,9),(2,10),(2,16),(4,7),(4,9),(4,10),(4,16),(7,9),(7,10),(7,16),(9,10),(9,16),(10,16)]

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

noncomputable def certificate_2560_q : Finset ℕ := ([0,1,2,4,7,9,11,14] : List ℕ).toFinset
noncomputable def certificate_2560_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,11),(0,14),(1,2),(1,4),(1,7),(1,9),(1,11),(1,14),(2,4),(2,7),(2,9),(2,11),(2,14),(4,7),(4,9),(4,11),(4,14),(7,9),(7,11),(7,14),(9,11),(9,14),(11,14)]

noncomputable def certificate_2561_q : Finset ℕ := ([0,1,2,4,7,9,11,15] : List ℕ).toFinset
noncomputable def certificate_2561_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,11),(0,15),(1,2),(1,4),(1,7),(1,9),(1,11),(1,15),(2,4),(2,7),(2,9),(2,11),(2,15),(4,7),(4,9),(4,11),(4,15),(7,9),(7,11),(7,15),(9,11),(9,15),(11,15)]

noncomputable def certificate_2562_q : Finset ℕ := ([0,1,2,4,7,9,11,16] : List ℕ).toFinset
noncomputable def certificate_2562_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,9),(0,11),(0,16),(1,2),(1,4),(1,7),(1,9),(1,11),(1,16),(2,4),(2,7),(2,9),(2,11),(2,16),(4,7),(4,9),(4,11),(4,16),(7,9),(7,11),(7,16),(9,11),(9,16),(11,16)]

noncomputable def certificate_2563_q : Finset ℕ := ([0,1,2,4,7,9,12,14] : List ℕ).toFinset
noncomputable def certificate_2563_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(0,14),(1,2),(1,4),(1,7),(1,9),(1,12),(1,14),(2,4),(2,7),(2,9),(2,12),(2,14),(4,7),(4,9),(4,12),(4,14),(7,9),(7,12),(7,14),(9,12),(9,14),(12,14)]

noncomputable def certificate_2564_q : Finset ℕ := ([0,1,2,4,7,9,12,15] : List ℕ).toFinset
noncomputable def certificate_2564_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(0,15),(1,2),(1,4),(1,7),(1,9),(1,12),(1,15),(2,4),(2,7),(2,9),(2,12),(2,15),(4,7),(4,9),(4,12),(4,15),(7,9),(7,12),(7,15),(9,12),(9,15),(12,15)]

noncomputable def certificate_2565_q : Finset ℕ := ([0,1,2,4,7,9,12,16] : List ℕ).toFinset
noncomputable def certificate_2565_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,9),(0,12),(0,16),(1,2),(1,4),(1,7),(1,9),(1,12),(1,16),(2,4),(2,7),(2,9),(2,12),(2,16),(4,7),(4,9),(4,12),(4,16),(7,9),(7,12),(7,16),(9,12),(9,16),(12,16)]

noncomputable def certificate_2566_q : Finset ℕ := ([0,1,2,4,7,9,13,15] : List ℕ).toFinset
noncomputable def certificate_2566_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,9),(0,13),(0,15),(1,2),(1,4),(1,7),(1,9),(1,13),(1,15),(2,4),(2,7),(2,9),(2,13),(2,15),(4,7),(4,9),(4,13),(4,15),(7,9),(7,13),(7,15),(9,13),(9,15),(13,15)]

noncomputable def certificate_2567_q : Finset ℕ := ([0,1,2,4,7,9,13,16] : List ℕ).toFinset
noncomputable def certificate_2567_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,9),(0,13),(0,16),(1,2),(1,4),(1,7),(1,9),(1,13),(1,16),(2,4),(2,7),(2,9),(2,13),(2,16),(4,7),(4,9),(4,13),(4,16),(7,9),(7,13),(7,16),(9,13),(9,16),(13,16)]

noncomputable def certificate_2568_q : Finset ℕ := ([0,1,2,4,7,9,14,16] : List ℕ).toFinset
noncomputable def certificate_2568_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,9),(0,14),(0,16),(1,2),(1,4),(1,7),(1,9),(1,14),(1,16),(2,4),(2,7),(2,9),(2,14),(2,16),(4,7),(4,9),(4,14),(4,16),(7,9),(7,14),(7,16),(9,14),(9,16),(14,16)]

noncomputable def certificate_2569_q : Finset ℕ := ([0,1,2,4,7,10,11,14] : List ℕ).toFinset
noncomputable def certificate_2569_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(0,1),(0,2),(0,4),(0,7),(0,10),(0,11),(0,14),(1,2),(1,4),(1,7),(1,10),(1,11),(1,14),(2,4),(2,7),(2,10),(2,11),(2,14),(4,7),(4,10),(4,11),(4,14),(7,10),(7,11),(7,14),(10,11),(10,14),(11,14)]

noncomputable def certificate_2570_q : Finset ℕ := ([0,1,2,4,7,10,11,15] : List ℕ).toFinset
noncomputable def certificate_2570_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,10),(0,11),(0,15),(1,2),(1,4),(1,7),(1,10),(1,11),(1,15),(2,4),(2,7),(2,10),(2,11),(2,15),(4,7),(4,10),(4,11),(4,15),(7,10),(7,11),(7,15),(10,11),(10,15),(11,15)]

noncomputable def certificate_2571_q : Finset ℕ := ([0,1,2,4,7,10,11,16] : List ℕ).toFinset
noncomputable def certificate_2571_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,10),(0,11),(0,16),(1,2),(1,4),(1,7),(1,10),(1,11),(1,16),(2,4),(2,7),(2,10),(2,11),(2,16),(4,7),(4,10),(4,11),(4,16),(7,10),(7,11),(7,16),(10,11),(10,16),(11,16)]

noncomputable def certificate_2572_q : Finset ℕ := ([0,1,2,4,7,10,12,15] : List ℕ).toFinset
noncomputable def certificate_2572_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(0,1),(0,2),(0,4),(0,7),(0,10),(0,12),(0,15),(1,2),(1,4),(1,7),(1,10),(1,12),(1,15),(2,4),(2,7),(2,10),(2,12),(2,15),(4,7),(4,10),(4,12),(4,15),(7,10),(7,12),(7,15),(10,12),(10,15),(12,15)]

noncomputable def certificate_2573_edges : List (ℕ × ℕ) := [(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(0,1),(0,2),(0,4),(0,7),(0,10),(0,12),(0,16),(1,2),(1,4),(1,7),(1,10),(1,12),(1,16),(2,4),(2,7),(2,10),(2,12),(2,16),(4,7),(4,10),(4,12),(4,16),(7,10),(7,12),(7,16),(10,12),(10,16),(12,16)]

end CycleClique

end OAI
end


