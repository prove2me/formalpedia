-- Prove2me | Definitions.Def_OAIQ106E040
-- name    : OAIQ106E040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T01:03:29.797113+00:00
-- url     : https://prove2.me/theorems/10be9cb5-2a9f-4bc4-a779-5a5bc293864e
-- title:
--   Definitions bundle OAIQ106E040 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.rows11_11`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_3`, `OAI.MUB6.Certificate.GramEntries.Block5.rows11_8`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block5Row11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block5Row11.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E018`, `OAIQ106E035` and `OAIQ106E039` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramAssembly.Block5.indexed_entry_eval_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_11_e`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_3_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E035
import Definitions.Def_OAIQ106E039

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_3 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row19784, row19785, row19786, row19787, row19788, row19789, row19790, row19791, row19792, row19793, row19794, row19795, row19796, row19797, row19798, row19799, row19800, row19801, row19802, row19803, row19804, row19805, row19806, row19807, row19808, row19809, row19810, row19811, row19812, row19813, row19814, row19815, row19816, row19817, row19818, row19819, row19820, row19821, row19822, row19823, row19824, row19825, row19826, row19827, row19828, row19829, row19830, row19831, row19832, row19833, row19834, row19835, row19836, row19837, row19838, row19839, row19840, row19841, row19842, row19843]

def rows11_8 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20084, row20085, row20086, row20087, row20088, row20089, row20090, row20091, row20092, row20093, row20094, row20095, row20096, row20097, row20098, row20099, row20100, row20101, row20102, row20103, row20104, row20105, row20106, row20107, row20108, row20109, row20110, row20111, row20112, row20113, row20114, row20115, row20116, row20117, row20118, row20119, row20120, row20121, row20122, row20123, row20124, row20125, row20126, row20127, row20128, row20129, row20130, row20131, row20132, row20133, row20134, row20135, row20136, row20137, row20138, row20139, row20140, row20141, row20142, row20143]

def rows11_11 : Fin GramFunctions.Block5.form11.size → Integer.Sparse Key := ![row20264, row20265, row20266, row20267, row20268, row20269, row20270, row20271, row20272, row20273, row20274, row20275, row20276, row20277, row20278, row20279, row20280, row20281, row20282, row20283, row20284, row20285, row20286, row20287, row20288, row20289, row20290, row20291, row20292, row20293, row20294, row20295, row20296, row20297, row20298, row20299, row20300, row20301, row20302, row20303, row20304, row20305, row20306, row20307, row20308, row20309, row20310, row20311, row20312, row20313, row20314, row20315, row20316, row20317, row20318, row20319, row20320, row20321, row20322, row20323]

end MUB6.Certificate.GramEntries.Block5

end OAI
end


