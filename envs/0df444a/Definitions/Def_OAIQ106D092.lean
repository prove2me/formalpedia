-- Prove2me | Definitions.Def_OAIQ106D092
-- name    : OAIQ106D092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:58:46.521968+00:00
-- url     : https://prove2.me/theorems/34a76956-bdd5-4db5-875a-342f3cd3bfc1
-- title:
--   Definitions bundle OAIQ106D092 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1251 declarations of OpenAI's Lean: 1251 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block4.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block4.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_8`, `OAI.MUB6.Certificate.GramEntries.Block4.entry12_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry13_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry14_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_1`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_2`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_3`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_4`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_6`, `OAI.MUB6.Certificate.GramEntries.Block4.entry15_8` and 1211 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block4Data`, `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block16`, `MutuallyUnbiased_GramKeys_Block17`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block20`, `MutuallyUnbiased_GramKeys_Block21`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block24`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block6`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block134`, `MutuallyUnbiased_GramRows_Block135`, `MutuallyUnbiased_GramRows_Block136`, `MutuallyUnbiased_GramRows_Block137`, `MutuallyUnbiased_GramRows_Block138`, `MutuallyUnbiased_GramRows_Block139`, `MutuallyUnbiased_GramRows_Block140`, `MutuallyUnbiased_GramRows_Block141`, `MutuallyUnbiased_GramRows_Block142`, `MutuallyUnbiased_GramRows_Block144`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block84`, `MutuallyUnbiased_GramRows_Block85`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block88`, `MutuallyUnbiased_GramRows_Block89`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_MixedSemantics_Values15`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D155`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D162`, `OAIQ106D163`, `OAIQ106D164`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D167`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172`, `OAIQ106D178` and `OAIQ106D184`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key53 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key54 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key55 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key56 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key57 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key58 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key59 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key60 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key61 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key62 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key63 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key64 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key65 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key68 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key72 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key77 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key82 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 2), (1, -1), (1, -1), (1, 1)]⟩
def key87 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key89 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key95 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key121 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩
def key122 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩
def key123 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
def key124 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩
def key125 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key126 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key127 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key128 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key135 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key157 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩
def key180 : Key := ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key198 : Key := ⟨0, 0, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key199 : Key := ⟨0, 0, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩
def key220 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key221 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key225 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1283 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key1358 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key1360 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 3), (2, 0)]⟩
def key1364 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key1372 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key1374 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 1), (0, 2), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1486 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 3), (2, 0)]⟩
def key1490 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key1495 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key1500 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 2), (2, 1)]⟩
def key1501 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 3), (2, 0)]⟩
def key1503 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
def key1506 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key1507 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key1511 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 0), (0, 3), (2, -2)]⟩
def key1513 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 1), (0, 2), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1701 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key1706 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key1712 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 3), (2, 0)]⟩
def key1716 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
def key1721 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key1723 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key1727 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 1), (0, 1), (0, 1), (2, -1)]⟩
def key1732 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 2), (2, 1)]⟩
def key1733 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 3), (2, 0)]⟩
def key1735 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 3), (2, -1)]⟩
def key1736 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 1), (0, 2), (2, -1)]⟩
def key1739 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 0), (0, 3), (2, -2)]⟩
def key1741 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 1), (0, 2), (2, -2)]⟩
def key1751 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 1), (0, 2), (2, -3)]⟩
def key1756 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1854 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key1860 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 1), (2, 1)]⟩
def key1863 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (1, 1), (1, 1)]⟩
def key1872 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, 1), (0, 1), (1, -1), (1, 0)]⟩
def key1874 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, -1), (0, 2), (2, 0)]⟩
def key1875 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, 0), (0, 2), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1930 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key1948 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, 1), (1, -1), (1, 0)]⟩
def key1950 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 0), (1, -2), (1, 1)]⟩
def key1952 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 1), (1, -1), (1, -1)]⟩
def key1959 : Key := ⟨0, 1, [(-2, 3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 0)]⟩
def key1961 : Key := ⟨0, 1, [(-2, 3), (0, -2), (0, 0), (0, 0), (1, -1), (1, 0)]⟩
def key1963 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, -1), (1, 0), (1, 0)]⟩
def key1965 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, 0), (1, -1), (1, 0)]⟩
def key1967 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, 0), (0, 0), (1, -2), (1, 0)]⟩
def key1968 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, 0), (0, 0), (1, -1), (1, -1)]⟩
def key1970 : Key := ⟨0, 1, [(-2, 3), (0, 0), (0, 0), (0, 0), (1, -2), (1, -1)]⟩
def key1971 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1972 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1973 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩
def key1974 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩
def key1975 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1976 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1977 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1978 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1979 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (0, 0), (3, 2)]⟩
def key1980 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (0, 1), (3, 1)]⟩
def key1981 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩
def key1982 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩
def key1983 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1984 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (0, 0), (3, 1)]⟩
def key1985 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩
def key1989 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key1990 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key1991 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key1993 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key1994 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key1996 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (0, 0), (3, 1)]⟩
def key1997 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩
def key2001 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (1, 2)]⟩
def key2008 : Key := ⟨0, 1, [(-1, -3), (-1, 2), (0, 0), (0, 0), (1, 0), (1, 1)]⟩
def key2010 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2011 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (3, 2)]⟩
def key2012 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 2), (3, 1)]⟩
def key2013 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩
def key2014 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩
def key2015 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2016 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (0, 1), (3, 1)]⟩
def key2017 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩
def key2018 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2019 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2020 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (0, 0), (3, 2)]⟩
def key2021 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (0, 1), (3, 1)]⟩
def key2022 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩
def key2023 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩
def key2024 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩
def key2025 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 2), (0, 0), (0, 0), (3, 1)]⟩
def key2026 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩
def key2027 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key2028 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key2029 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (0, 3), (2, 0)]⟩
def key2030 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (1, 0), (1, 3)]⟩
def key2032 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key2033 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key2034 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key2037 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key2039 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩
def key2040 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 1), (3, 2)]⟩
def key2041 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 2), (3, 1)]⟩
def key2042 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩
def key2043 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 2), (2, 1)]⟩
def key2044 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩
def key2045 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2046 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -1)]⟩
def key2047 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2048 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (0, 0), (3, 2)]⟩
def key2049 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (0, 1), (3, 1)]⟩
def key2050 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, 1)]⟩
def key2051 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, 0)]⟩
def key2052 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -1)]⟩
def key2053 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -1)]⟩
def key2054 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 2), (0, -1), (0, 0), (3, 1)]⟩
def key2055 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩
def key2056 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩
def key2057 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (0, 1), (2, 2)]⟩
def key2058 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (0, 2), (2, 1)]⟩
def key2059 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (0, 3), (2, 0)]⟩
def key2060 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (1, 0), (1, 3)]⟩
def key2062 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (0, 1), (2, 1)]⟩
def key2063 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
def key2069 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key2072 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -1)]⟩
def key2074 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (-1, 1), (0, -1), (0, 0), (3, 1)]⟩
def key2075 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (-1, 1), (0, -1), (1, 1), (2, 0)]⟩
def key2076 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -1)]⟩
def key2100 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 0), (3, 3)]⟩
def key2101 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 1), (3, 2)]⟩
def key2102 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 2), (2, 1)]⟩
def key2103 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 3), (2, 0)]⟩
def key2104 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 1), (1, 2), (2, 0)]⟩
def key2105 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩
def key2106 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 1), (3, 2)]⟩
def key2107 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 2), (2, 1)]⟩
def key2108 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩
def key2109 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2110 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 1), (1, 2), (2, -1)]⟩
def key2111 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 1), (0, -1), (0, 0), (3, 2)]⟩
def key2112 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 1), (0, -1), (1, 2), (2, 0)]⟩
def key2113 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (-1, 1), (0, 0), (1, 2), (2, -1)]⟩
def key2120 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key2121 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key2122 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key2123 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key2124 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 0), (3, 3)]⟩
def key2125 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 1), (3, 2)]⟩
def key2126 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 2), (3, 1)]⟩
def key2127 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 1), (2, 2)]⟩
def key2128 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 2), (2, 1)]⟩
def key2129 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, 0)]⟩
def key2130 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (0, -1), (3, 3)]⟩
def key2131 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -1)]⟩
def key2132 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -2)]⟩
def key2133 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -2)]⟩
def key2134 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -2)]⟩
def key2135 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 0), (3, 2)]⟩
def key2138 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, 0)]⟩
def key2139 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, -1), (3, 2)]⟩
def key2140 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, -1)]⟩
def key2141 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -2)]⟩
def key2143 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -2), (0, 0), (3, 1)]⟩
def key2144 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, 0)]⟩
def key2145 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -2)]⟩
def key2146 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (2, 2)]⟩
def key2147 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (0, 2), (2, 1)]⟩
def key2148 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (0, 3), (2, 0)]⟩
def key2149 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (1, 0), (1, 3)]⟩
def key2151 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (0, 1), (2, 1)]⟩
def key2152 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (0, 2), (2, 0)]⟩
def key2160 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 3), (2, -1)]⟩
def key2161 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 3)]⟩
def key2162 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 1), (0, 2), (2, -1)]⟩
def key2163 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, 1), (1, -1), (1, 2)]⟩
def key2166 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (2, -2)]⟩
def key2169 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2185 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, 0), (0, 2), (2, -1)]⟩
def key2186 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 2)]⟩
def key2207 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (0, 1), (3, 2)]⟩
def key2208 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (0, 2), (3, 1)]⟩
def key2209 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 1), (2, 2)]⟩
def key2210 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 2), (2, 1)]⟩
def key2211 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (0, -1), (3, 3)]⟩
def key2212 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, -1)]⟩
def key2213 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -2)]⟩
def key2214 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -3)]⟩
def key2215 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -3)]⟩
def key2216 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (0, 0), (3, 2)]⟩
def key2217 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (0, 1), (3, 1)]⟩
def key2218 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 1), (2, 1)]⟩
def key2219 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 2), (2, 0)]⟩
def key2220 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -2), (0, -1), (3, 2)]⟩
def key2223 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -3)]⟩
def key2224 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -3)]⟩
def key2225 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (0, 0), (3, 1)]⟩
def key2226 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (1, 1), (2, 0)]⟩
def key2227 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -2), (0, -1), (3, 1)]⟩
def key2228 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, -1)]⟩
def key2229 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -2)]⟩
def key2230 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -3)]⟩
def key2234 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 1), (2, 1)]⟩
def key2235 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 2), (2, 0)]⟩
def key2236 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (1, 2)]⟩
def key2238 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 2), (1, 0), (1, 1)]⟩
def key2239 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (0, 1), (2, 2)]⟩
def key2240 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (0, 2), (2, 1)]⟩
def key2241 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (0, 3), (2, 0)]⟩
def key2242 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (1, 0), (1, 3)]⟩
def key2246 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 1), (0, 2), (2, -1)]⟩
def key2249 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 3), (2, -1)]⟩
def key2250 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, -1), (1, -1), (1, 3)]⟩
def key2253 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 1), (0, 2), (2, -2)]⟩
def key2259 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩
def key2261 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (0, 0), (3, 1)]⟩
def key2262 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (1, 1), (2, 0)]⟩
def key2266 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -3)]⟩
def key2270 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 2)]⟩
def key2286 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, -1), (1, -1), (1, 2)]⟩
def key2301 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -3), (0, 0), (1, 0), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key357 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 1), (2, 2)]⟩
def key358 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 3), (2, 0)]⟩
def key359 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
def key360 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key363 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key364 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key365 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key368 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 1), (0, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2685 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2727 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2953 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩
def key3069 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, -1), (1, 0), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key3090 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 1), (0, -1), (1, 0), (2, 2)]⟩
def key3106 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 0), (2, 2)]⟩
def key3109 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (1, -1), (2, 2)]⟩
def key3131 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 0), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key492 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key493 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key496 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key497 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key502 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 1), (0, 1), (0, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key515 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key517 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (1, 0), (1, 2)]⟩
def key527 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 1), (2, 2)]⟩
def key528 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 3), (2, 0)]⟩
def key529 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 0), (2, 2)]⟩
def key531 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 2), (2, 0)]⟩
def key532 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 3), (2, -1)]⟩
def key534 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 1), (0, 1), (2, 0)]⟩
def key535 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 1), (0, 2), (2, -1)]⟩
def key536 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 2), (1, 0), (1, 0)]⟩
def key537 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key540 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 1), (0, 1), (2, -1)]⟩
def key544 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 2), (1, -1), (1, 0)]⟩
def key547 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 0), (0, 2), (2, -2)]⟩
def key549 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 0), (1, -2), (1, 2)]⟩
def key551 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 1), (0, 2), (2, -3)]⟩
def key556 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -1), (1, -1)]⟩
def key621 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key624 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 2), (1, 0), (1, 0)]⟩
def key633 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, -1), (1, 0), (1, 2)]⟩
def key635 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 0), (1, -1), (1, 2)]⟩
def key637 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 1), (1, 0), (1, 0)]⟩
def key638 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 2), (1, -1), (1, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key643 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0)]⟩
def key644 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 2), (1, -1), (1, -1)]⟩
def key651 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -1), (1, -1)]⟩
def key652 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 2), (1, -3), (1, 0)]⟩
def key664 : Key := ⟨0, 0, [(-2, 2), (0, -3), (0, 0), (0, 0), (0, 1), (2, 0)]⟩
def key674 : Key := ⟨0, 0, [(-2, 2), (0, -1), (0, -1), (0, -1), (0, 1), (2, 0)]⟩
def key675 : Key := ⟨0, 0, [(-2, 2), (0, -1), (0, -1), (0, 0), (0, 1), (2, -1)]⟩
def key676 : Key := ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 0), (0, 0), (2, -1)]⟩
def key681 : Key := ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 0), (0, 1), (2, -3)]⟩
def key688 : Key := ⟨0, 0, [(-2, 3), (0, -1), (0, -1), (0, -1), (1, 0), (1, 0)]⟩
def key689 : Key := ⟨0, 0, [(-2, 3), (0, -1), (0, -1), (0, 0), (1, -1), (1, 0)]⟩
def key691 : Key := ⟨0, 0, [(-2, 3), (0, -1), (0, 0), (0, 0), (1, -1), (1, -1)]⟩
def key693 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 1), (2, 2)]⟩
def key694 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 0), (1, 2), (2, 1)]⟩
def key695 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩
def key696 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, 0)]⟩
def key697 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, 0)]⟩
def key698 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, 1)]⟩
def key699 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩
def key700 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩
def key704 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key705 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key706 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key707 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key709 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key710 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key712 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩
def key716 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 0), (1, 2)]⟩
def key723 : Key := ⟨0, 0, [(-1, -3), (-1, 2), (0, 0), (0, 0), (1, 0), (1, 1)]⟩
def key731 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key733 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key756 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 0), (3, 3)]⟩
def key757 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 1), (2, 2)]⟩
def key758 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 3), (2, 0)]⟩
def key759 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, -1), (0, 2), (1, 1), (2, 0)]⟩
def key760 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩
def key761 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩
def key762 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩
def key763 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, 1), (2, 1)]⟩
def key764 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩
def key765 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 1), (1, 1), (2, 0)]⟩
def key766 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩
def key767 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 1), (0, 0), (1, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key768 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩
def key769 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩
def key773 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (1, 2)]⟩
def key775 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 2), (1, 0), (1, 1)]⟩
def key777 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key779 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key780 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key782 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key783 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key785 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key787 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (0, -1), (3, 3)]⟩
def key788 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, 1), (2, 1)]⟩
def key789 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -1)]⟩
def key790 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, 1), (2, -1)]⟩
def key791 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, 0)]⟩
def key792 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 1), (2, -1)]⟩
def key793 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -1)]⟩
def key800 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (1, 2)]⟩
def key802 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (2, 1)]⟩
def key804 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 3), (2, -1)]⟩
def key805 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 3)]⟩
def key807 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 1), (0, 1), (2, 0)]⟩
def key808 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 1), (0, 2), (2, -1)]⟩
def key810 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 2), (1, -1), (1, 1)]⟩
def key812 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 1), (0, 1), (2, -1)]⟩
def key821 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (2, 0)]⟩
def key824 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -1)]⟩
def key835 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, -1), (1, 0), (1, 1)]⟩
def key837 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, 0), (0, 1), (2, -1)]⟩
def key838 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, 0), (1, -1), (1, 1)]⟩
def key845 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 1), (2, 2)]⟩
def key846 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 2), (2, 1)]⟩
def key847 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, 2), (2, -3)]⟩
def key848 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -3)]⟩
def key850 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 2), (2, 0)]⟩
def key851 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, -1), (1, 1), (2, -1)]⟩
def key852 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, -3)]⟩
def key854 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 2), (0, -3), (1, 1), (2, 0)]⟩
def key855 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, -3)]⟩
def key858 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (1, 2)]⟩
def key859 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 1), (2, 1)]⟩
def key860 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (0, 2), (2, 0)]⟩
def key861 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (1, 2)]⟩
def key863 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 2), (1, 0), (1, 1)]⟩
def key865 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 0), (2, 2)]⟩
def key867 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 2), (2, 0)]⟩
def key871 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 0), (2, 2)]⟩
def key872 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 1), (2, 1)]⟩
def key873 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (0, 3), (2, -1)]⟩
def key874 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (1, -1), (1, 3)]⟩
def key876 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 0), (0, 2), (2, -1)]⟩
def key877 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 1), (0, 1), (2, -1)]⟩
def key886 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩
def key893 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key905 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, -1), (0, 1), (2, 0)]⟩
def key907 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (2, -1)]⟩
def key922 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 1), (2, 0)]⟩
def key923 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -3), (0, 0), (1, 0), (1, 1)]⟩
def key931 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, 0), (2, 0)]⟩
def key932 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, 1), (2, -1)]⟩
def key933 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, -1), (1, -1), (1, 1)]⟩
def key934 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 0), (0, 0), (2, -1)]⟩
def key938 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key940 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 0), (1, -3), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1047 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key1051 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key1057 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key1059 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key1063 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key1089 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key1092 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1097 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 0), (2, 1)]⟩
def key1105 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key1110 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key1113 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 0), (2, 1)]⟩
def key1133 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩
def key1137 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩
def key1139 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, -1), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1204 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩
def key1206 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩
def key1278 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 2), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block4

open GramRows GramNormalization

def entry4_2 : Integer.Sparse Key := [(key972, 144), (key978, -144), (key1086, -144), (key1092, 288), (key1163, -144), (key1227, -144), (key1244, 144)]

def entry6_0 : Integer.Sparse Key := [(key2378, -24), (key2383, 36), (key2390, 80), (key2394, -60), (key2411, 12), (key2437, 56), (key2443, -36), (key2472, -48), (key2480, 72), (key2484, -12), (key2509, 60), (key2524, -72), (key2580, 16), (key2587, -120), (key2593, 108), (key2598, 64), (key2600, -84), (key2766, -72), (key2772, 60), (key2843, -24), (key2880, 72), (key2887, 72), (key2889, -60), (key2910, -72), (key2929, 16), (key2931, -36), (key2966, -72), (key2968, 84), (key2989, -72), (key3002, 56)]

def entry6_4 : Integer.Sparse Key := [(key1029, 144), (key1035, -144), (key1107, -144), (key1113, 288), (key1122, -144), (key1231, -144), (key1234, 144)]

def entry6_6 : Integer.Sparse Key := [(key2608, 72), (key2614, -72), (key2624, -72), (key2630, 144), (key2638, -120), (key2657, -24), (key2659, 72), (key2663, 36), (key2669, -36), (key2698, -80), (key2704, 84), (key2724, -72), (key2757, 56), (key2778, 8), (key2784, 60), (key2792, -72), (key2801, 72), (key2807, -36), (key2827, -80), (key2851, -36), (key2858, -24), (key2868, 84), (key2918, -48), (key2919, 72), (key3009, 16), (key3011, 8), (key3016, 36), (key3021, 60), (key3022, -72), (key3025, -36)]

def entry7_4 : Integer.Sparse Key := [(key1047, -288), (key1057, 288), (key1133, 288), (key1137, -288)]

def entry8_4 : Integer.Sparse Key := [(key971, 144), (key975, -144), (key1085, -144), (key1089, 288), (key1161, -144), (key1179, -144), (key1217, 144)]

def entry9_0 : Integer.Sparse Key := [(key1975, 288), (key1980, -576), (key1996, 288)]

def entry9_1 : Integer.Sparse Key := [(key55, -288), (key61, 288), (key123, 288), (key126, -288)]

def entry9_2 : Integer.Sparse Key := [(key1972, -288), (key1984, 288), (key2208, 288), (key2225, -288)]

def entry9_3 : Integer.Sparse Key := [(key2010, 288), (key2039, -288), (key2124, -288), (key2211, 288)]

def entry9_4 : Integer.Sparse Key := [(key53, -288), (key59, 288), (key121, 288), (key124, -288)]

def entry9_5 : Integer.Sparse Key := [(key57, 288), (key64, -576), (key77, 288)]

def entry9_6 : Integer.Sparse Key := [(key2012, -288), (key2025, 288), (key2041, 288), (key2054, -288)]

def entry9_7 : Integer.Sparse Key := [(key2100, 288), (key2105, -576), (key2130, 288)]

def entry9_8 : Integer.Sparse Key := [(key1971, -288), (key1979, 288), (key2207, 288), (key2216, -288)]

def entry9_9 : Integer.Sparse Key := [(key756, 288), (key760, -576), (key787, 288)]

def entry10_0 : Integer.Sparse Key := [(key2378, -144), (key2381, 144), (key2390, 144), (key2392, -144), (key2406, -72), (key2409, 72), (key2437, 72), (key2440, -72), (key2472, -72), (key2480, 144), (key2482, -72), (key2503, -72), (key2506, 144), (key2522, -72), (key2538, 72), (key2543, -72), (key2554, -72), (key2563, 72)]

def entry10_4 : Integer.Sparse Key := [(key1028, 144), (key1032, -144), (key1106, -144), (key1110, 288), (key1120, -144), (key1189, -144), (key1196, 144)]

def entry10_6 : Integer.Sparse Key := [(key2609, 72), (key2613, -72), (key2625, -72), (key2629, 144), (key2637, -72), (key2647, -72), (key2652, 72), (key2664, 36), (key2668, -36), (key2699, -36), (key2703, 72), (key2723, -36), (key2736, -36), (key2746, 36), (key2779, -36), (key2783, 72), (key2791, -36), (key2802, 72), (key2806, -36), (key2826, -36), (key2852, -36), (key2857, -36), (key2867, 72), (key2894, -36), (key2896, 72), (key2903, -36), (key2937, -36), (key2942, 36), (key2949, -36), (key2959, 36), (key2973, 72), (key2975, -36), (key2982, -36)]

def entry10_9 : Integer.Sparse Key := [(key2011, -288), (key2020, 288), (key2040, 288), (key2048, -288)]

def entry10_10 : Integer.Sparse Key := [(key2608, 72), (key2611, -72), (key2624, -72), (key2627, 144), (key2636, -120), (key2645, -24), (key2651, 72), (key2663, 36), (key2666, -36), (key2698, -80), (key2701, 84), (key2722, -72), (key2745, 56), (key2778, 8), (key2781, 60), (key2790, -72), (key2801, 72), (key2804, -36), (key2825, -80), (key2851, -36), (key2856, -24), (key2866, 84), (key2892, -48), (key2895, 72), (key2941, 16), (key2947, 8), (key2958, 36), (key2971, 60), (key2974, -72), (key2981, -36)]

def entry11_1 : Integer.Sparse Key := [(key220, 144), (key225, -144), (key492, -144), (key497, 288), (key551, -144), (key664, -144), (key681, 144)]

def entry11_3 : Integer.Sparse Key := [(key1360, -144), (key1372, 144), (key1486, -144), (key1511, 144), (key1712, 288), (key1721, -144), (key1739, -144)]

def entry11_7 : Integer.Sparse Key := [(key1501, -288), (key1506, 288), (key1733, 288), (key1735, -288)]

def entry11_9 : Integer.Sparse Key := [(key358, -288), (key363, 288), (key528, 288), (key532, -288)]

def entry12_6 : Integer.Sparse Key := [(key2378, -24), (key2383, 6), (key2390, 36), (key2394, -6), (key2406, -72), (key2411, 42), (key2437, -36), (key2443, 42), (key2472, -48), (key2480, 144), (key2484, -42), (key2503, 60), (key2509, -54), (key2524, 24), (key2569, 24), (key2571, -36), (key2576, 12), (key2580, -36), (key2587, -48), (key2593, 66), (key2598, 36), (key2600, -66), (key2766, -36), (key2772, 66), (key2843, -60), (key2880, 84), (key2887, 72), (key2889, -66), (key2910, -72), (key2931, -6), (key2966, -24), (key2968, -18), (key2989, 24), (key2995, 12)]

def entry12_8 : Integer.Sparse Key := [(key2361, -144), (key2364, 144), (key2456, -144), (key2517, 288), (key2520, -144), (key2531, 144), (key2561, -144)]

def entry12_9 : Integer.Sparse Key := [(key1975, 288), (key1980, -288), (key2217, -288), (key2261, 288)]

def entry12_10 : Integer.Sparse Key := [(key2378, -72), (key2381, 72), (key2390, 72), (key2392, -72), (key2406, -108), (key2409, 108), (key2437, -36), (key2440, 36), (key2472, -108), (key2480, 216), (key2482, -108), (key2503, 36), (key2506, -72), (key2522, 36), (key2538, 108), (key2543, -108), (key2554, 36), (key2563, -36)]

def entry13_0 : Integer.Sparse Key := [(key2390, 32), (key2437, 32), (key2580, 16), (key2587, -72), (key2593, 72), (key2598, 40), (key2600, -72), (key2766, -72), (key2772, 72), (key2843, 144), (key2880, 144), (key2887, -72), (key2889, -72), (key2910, -144), (key2929, 40), (key2931, -72), (key2966, -72), (key2968, -72), (key2989, -144), (key2995, 144), (key3002, 128)]

def entry13_6 : Integer.Sparse Key := [(key2608, 36), (key2614, -36), (key2624, -36), (key2630, 72), (key2638, -72), (key2659, 36), (key2663, 36), (key2669, -36), (key2698, -54), (key2704, -6), (key2724, -108), (key2752, 72), (key2757, 80), (key2778, -18), (key2784, 42), (key2792, -36), (key2801, -36), (key2807, -36), (key2827, -68), (key2851, 72), (key2858, 66), (key2868, 102), (key2918, -30), (key2919, -36), (key2922, -42), (key3009, 28), (key3011, 68), (key3016, 72), (key3021, 6), (key3022, -66), (key3025, -72)]

def entry13_9 : Integer.Sparse Key := [(key2025, 288), (key2054, -288), (key2143, -288), (key2227, 288)]

def entry13_10 : Integer.Sparse Key := [(key2609, 36), (key2613, -36), (key2625, -36), (key2629, 72), (key2637, -36), (key2647, -36), (key2652, 36), (key2664, 36), (key2668, -36), (key2699, -36), (key2703, -36), (key2723, -72), (key2736, 72), (key2746, 72), (key2779, -36), (key2783, 72), (key2791, -36), (key2802, -36), (key2806, -36), (key2826, -72), (key2852, 72), (key2857, 72), (key2867, 144), (key2894, -36), (key2896, -36), (key2903, -72), (key2937, -36), (key2942, 36), (key2949, 72), (key2959, 72), (key2973, -36), (key2975, -36), (key2982, -72)]

def entry13_11 : Integer.Sparse Key := [(key1364, -144), (key1374, 144), (key1490, -144), (key1513, 144), (key1716, 288), (key1723, -144), (key1741, -144)]

def entry13_12 : Integer.Sparse Key := [(key2378, 12), (key2383, 24), (key2390, -36), (key2394, -36), (key2406, 12), (key2411, 24), (key2437, -36), (key2443, -36), (key2472, -48), (key2480, 48), (key2484, -24), (key2503, 48), (key2509, -24), (key2524, 72), (key2587, 24), (key2593, 84), (key2600, -72), (key2766, 24), (key2772, 84), (key2843, -24), (key2880, 72), (key2887, -12), (key2889, -84), (key2910, -72), (key2931, -72), (key2966, -12), (key2968, -84), (key2989, -72), (key2995, 144), (key3002, 72)]

def entry13_13 : Integer.Sparse Key := [(key2608, 72), (key2614, 72), (key2624, -72), (key2630, -36), (key2638, -80), (key2657, 8), (key2659, 36), (key2663, 72), (key2669, 72), (key2698, -84), (key2704, -60), (key2724, -72), (key2757, 56), (key2778, -60), (key2784, -12), (key2792, -72), (key2801, -72), (key2807, -36), (key2827, -80), (key2851, 144), (key2858, 120), (key2868, 120), (key2918, 24), (key2919, -36), (key2922, -36), (key3009, 16), (key3011, 8), (key3016, 36), (key3021, 24), (key3022, -36), (key3025, -36)]

def entry14_0 : Integer.Sparse Key := [(key2378, 24), (key2383, -24), (key2390, -24), (key2394, 24), (key2406, -24), (key2411, 24), (key2437, 24), (key2443, -24), (key2480, -72), (key2484, 72), (key2503, 72), (key2509, -72), (key2587, 48), (key2593, -48), (key2598, -48), (key2600, 48), (key2766, -48), (key2772, 48), (key2887, -144), (key2889, 144), (key2929, 48), (key2931, -48), (key2966, 144), (key2968, -144)]

def entry14_2 : Integer.Sparse Key := [(key2370, 96), (key2376, -84), (key2388, 12), (key2398, -96), (key2404, 84), (key2435, -12), (key2478, 96), (key2501, -96), (key2570, -48), (key2575, 48), (key2583, 48), (key2589, -60), (key2604, -12), (key2762, -48), (key2768, 60), (key2916, 48), (key2925, -96), (key3005, 12), (key3019, -48), (key3028, 96)]

def entry14_6 : Integer.Sparse Key := [(key2608, -36), (key2614, 36), (key2624, 36), (key2630, -72), (key2638, 48), (key2657, 24), (key2659, -36), (key2663, 36), (key2669, -36), (key2698, 114), (key2704, -42), (key2724, -24), (key2752, -12), (key2757, 12), (key2778, -42), (key2784, 6), (key2792, -24), (key2801, -108), (key2807, 108), (key2827, 8), (key2858, 54), (key2868, -54), (key2918, 54), (key2919, -108), (key2922, 18), (key3007, -12), (key3009, 24), (key3011, -8), (key3021, -54), (key3022, 90)]

def entry14_9 : Integer.Sparse Key := [(key2041, -288), (key2054, 288), (key2126, 288), (key2143, -288)]

def entry14_10 : Integer.Sparse Key := [(key2609, -36), (key2613, 36), (key2625, 36), (key2629, -72), (key2637, 36), (key2647, 36), (key2652, -36), (key2664, 36), (key2668, -36), (key2699, 108), (key2703, -108), (key2779, -36), (key2783, 72), (key2791, -36), (key2802, -108), (key2806, 108), (key2894, 108), (key2896, -108), (key2937, -36), (key2942, 36), (key2973, -108), (key2975, 108)]

def entry14_12 : Integer.Sparse Key := [(key2378, -48), (key2383, 36), (key2390, -72), (key2394, 48), (key2406, 48), (key2411, -36), (key2437, 72), (key2443, -48), (key2480, -84), (key2484, -12), (key2503, 84), (key2509, 12), (key2571, 48), (key2576, -48), (key2587, 12), (key2598, -36), (key2600, 60), (key2766, -12), (key2887, -96), (key2889, 48), (key2910, 96), (key2929, 36), (key2931, -60), (key2966, 96), (key2968, -48), (key2989, -96)]

def entry14_13 : Integer.Sparse Key := [(key2630, -108), (key2638, 4), (key2657, 68), (key2659, 36), (key2698, 36), (key2704, 24), (key2724, 108), (key2752, -84), (key2757, -12), (key2778, -36), (key2784, -24), (key2792, -60), (key2807, 108), (key2827, -4), (key2858, 36), (key2868, -36), (key2918, 36), (key2919, -36), (key2922, -24), (key3007, 36), (key3009, 12), (key3011, -68), (key3016, -36), (key3021, -36), (key3022, 24), (key3025, 36)]

def entry14_14 : Integer.Sparse Key := [(key2608, 72), (key2614, -72), (key2624, 72), (key2630, -36), (key2638, -56), (key2657, -16), (key2659, 36), (key2663, -72), (key2669, 72), (key2698, -132), (key2704, 60), (key2724, 48), (key2752, 24), (key2757, -48), (key2778, -12), (key2784, 12), (key2792, 48), (key2801, 72), (key2807, -36), (key2827, -56), (key2919, 108), (key2922, -108), (key3007, 24), (key3009, -24), (key3011, -16), (key3016, 36), (key3022, -108), (key3025, 108)]

def entry15_0 : Integer.Sparse Key := [(key2378, 72), (key2381, -72), (key2390, -72), (key2392, 72), (key2406, -72), (key2409, 72), (key2437, 72), (key2440, -72), (key2480, -216), (key2482, 216), (key2503, 216), (key2506, -216)]

def entry15_1 : Integer.Sparse Key := [(key994, 144), (key999, -144), (key1029, -144), (key1034, 144), (key1121, 144), (key1148, -144), (key1197, -144), (key1210, 144)]

def entry15_2 : Integer.Sparse Key := [(key2371, 144), (key2375, -144), (key2399, -144), (key2403, 144), (key2477, 144), (key2500, -144), (key2541, -144), (key2552, 144)]

def entry15_3 : Integer.Sparse Key := [(key2623, -144), (key2634, 144), (key2697, -144), (key2720, 144), (key2777, 144), (key2788, -144), (key2800, 144), (key2823, -144)]

def entry15_4 : Integer.Sparse Key := [(key993, 144), (key997, -144), (key1028, -144), (key1032, 144), (key1120, 144), (key1147, -144), (key1196, -144), (key1209, 144)]

def entry15_6 : Integer.Sparse Key := [(key2609, -36), (key2613, 36), (key2625, 36), (key2629, -72), (key2637, 36), (key2647, 36), (key2652, -36), (key2664, 36), (key2668, -36), (key2699, -36), (key2703, 72), (key2723, -36), (key2736, -36), (key2746, 36), (key2779, 108), (key2783, -108), (key2802, -108), (key2806, 108), (key2857, 108), (key2867, -108), (key2896, -108), (key2903, 108)]

def entry15_8 : Integer.Sparse Key := [(key2370, 96), (key2373, -84), (key2386, 12), (key2398, -96), (key2401, 84), (key2433, -12), (key2476, 96), (key2499, -96), (key2540, -48), (key2551, 48), (key2583, 48), (key2586, -60), (key2597, -12), (key2762, -48), (key2765, 60), (key2886, 48), (key2908, -96), (key2928, 12), (key2965, -48), (key2987, 96)]

def entry15_9 : Integer.Sparse Key := [(key2040, -288), (key2048, 288), (key2125, 288), (key2135, -288)]

def entry15_10 : Integer.Sparse Key := [(key2608, -36), (key2611, 36), (key2624, 36), (key2627, -72), (key2636, 48), (key2645, 24), (key2651, -36), (key2663, 36), (key2666, -36), (key2698, 114), (key2701, -42), (key2722, -24), (key2734, -12), (key2745, 12), (key2778, -42), (key2781, 6), (key2790, -24), (key2801, -108), (key2804, 108), (key2825, 8), (key2856, 54), (key2866, -54), (key2892, 54), (key2895, -108), (key2902, 18), (key2935, -12), (key2941, 24), (key2947, -8), (key2971, -54), (key2974, 90)]

def entry15_12 : Integer.Sparse Key := [(key2378, -36), (key2381, 36), (key2390, -108), (key2392, 108), (key2406, 36), (key2409, -36), (key2437, 108), (key2440, -108), (key2480, -180), (key2482, 36), (key2503, 180), (key2506, -36), (key2543, 144), (key2554, -144)]

def entry15_13 : Integer.Sparse Key := [(key2629, -108), (key2637, -36), (key2647, 108), (key2652, 36), (key2703, 108), (key2723, 36), (key2736, -108), (key2746, -36), (key2783, -108), (key2791, -36), (key2806, 108), (key2826, 36), (key2857, 72), (key2867, -72), (key2896, -36), (key2903, 36), (key2937, 108), (key2942, 36), (key2949, -108), (key2959, -36), (key2975, -36), (key2982, 36)]

def entry15_14 : Integer.Sparse Key := [(key2609, 72), (key2613, -72), (key2625, 72), (key2629, -36), (key2637, -36), (key2647, -36), (key2652, 36), (key2664, -72), (key2668, 72), (key2699, -72), (key2703, 36), (key2723, 36), (key2736, 36), (key2746, -36), (key2779, -72), (key2783, 36), (key2791, 36), (key2802, 72), (key2806, -36), (key2826, -36), (key2896, 108), (key2903, -108), (key2937, 36), (key2942, -36), (key2949, -36), (key2959, 36), (key2975, -108), (key2982, 108)]

def entry15_15 : Integer.Sparse Key := [(key2608, 72), (key2611, -72), (key2624, 72), (key2627, -36), (key2636, -56), (key2645, -16), (key2651, 36), (key2663, -72), (key2666, 72), (key2698, -132), (key2701, 60), (key2722, 48), (key2734, 24), (key2745, -48), (key2778, -12), (key2781, 12), (key2790, 48), (key2801, 72), (key2804, -36), (key2825, -56), (key2895, 108), (key2902, -108), (key2935, 24), (key2941, -24), (key2947, -16), (key2958, 36), (key2974, -108), (key2981, 108)]

def entry16_0 : Integer.Sparse Key := [(key2379, 36), (key2382, -60), (key2393, -68), (key2395, 72), (key2407, 36), (key2410, -36), (key2441, -80), (key2445, 60), (key2473, 16), (key2483, -36), (key2507, -72), (key2526, 60), (key2544, 8), (key2545, 24), (key2555, 8), (key2557, -12), (key2565, -36), (key2592, 108), (key2595, -84), (key2602, -76), (key2603, 72), (key2771, 36), (key2774, -36), (key2848, 56), (key2882, -72), (key2891, -36), (key2912, -80), (key2914, 120), (key2933, 8), (key2934, 12), (key2991, 136), (key2993, -60), (key2996, 12), (key3003, -36)]

def entry16_2 : Integer.Sparse Key := [(key2374, -60), (key2380, 24), (key2391, 12), (key2402, -108), (key2408, 96), (key2468, -72), (key2481, 96), (key2505, 24), (key2535, 108), (key2537, -72), (key2542, -72), (key2553, -48), (key2591, 60), (key2596, -24), (key2605, -12), (key2770, -36), (key2775, 48), (key2847, -72), (key2878, 180), (key2884, -72), (key2917, 48), (key2926, -72), (key3020, -24), (key3029, 48)]

def entry16_6 : Integer.Sparse Key := [(key2612, -36), (key2616, -36), (key2618, 42), (key2621, 30), (key2628, -36), (key2632, -36), (key2640, 102), (key2641, 54), (key2644, -36), (key2646, 42), (key2648, -36), (key2653, -42), (key2658, 18), (key2660, -30), (key2667, -36), (key2673, 30), (key2676, 6), (key2702, -12), (key2706, -12), (key2726, 72), (key2728, 36), (key2732, -30), (key2735, 36), (key2737, -30), (key2747, -36), (key2753, 6), (key2758, -18), (key2782, -24), (key2786, -24), (key2794, 36), (key2795, 30), (key2798, -6), (key2809, -36), (key2829, -28), (key2831, 36), (key2835, 54), (key2860, 42), (key2870, -12), (key2885, -30), (key2893, 30), (key2897, -30), (key2904, -30), (key2920, -6), (key2923, 30), (key2927, -36), (key2938, -6), (key2943, -18), (key2948, -8), (key2950, 18), (key2960, -28), (key2972, -24), (key2976, 42), (key2983, -12), (key2997, -6), (key3000, 18), (key3017, -8), (key3023, -6), (key3026, -24), (key3030, 54)]

def entry16_8 : Integer.Sparse Key := [(key2770, -144), (key2773, 144), (key2847, -144), (key2878, 288), (key2881, -144), (key2890, 144), (key2911, -144)]

def entry16_9 : Integer.Sparse Key := [(key2016, 288), (key2021, -288), (key2049, -288), (key2074, 288)]

def entry16_10 : Integer.Sparse Key := [(key2616, -72), (key2619, 72), (key2632, -72), (key2640, 144), (key2642, -72), (key2649, 72), (key2654, -72), (key2671, -36), (key2674, 36), (key2706, -36), (key2726, 72), (key2729, -36), (key2738, 36), (key2748, -36), (key2786, -36), (key2794, 72), (key2796, -36), (key2809, -36), (key2829, -36), (key2832, 72), (key2860, 72), (key2870, -36), (key2883, -36), (key2898, -36), (key2905, 72), (key2913, -36), (key2939, 36), (key2944, -36), (key2951, 36), (key2961, -36), (key2977, -36), (key2984, -36), (key2992, 72)]

def entry16_12 : Integer.Sparse Key := [(key2379, 30), (key2382, -18), (key2393, -10), (key2395, 12), (key2407, 78), (key2410, -42), (key2441, 32), (key2445, -30), (key2473, 52), (key2483, -42), (key2526, -30), (key2539, -48), (key2544, -56), (key2545, 84), (key2555, -80), (key2557, 54), (key2565, 42), (key2592, 42), (key2595, -54), (key2602, -62), (key2603, 60), (key2771, 30), (key2774, -66), (key2848, 56), (key2882, -60), (key2891, -66), (key2912, -52), (key2914, 132), (key2933, 4), (key2934, -6), (key2970, 36), (key2991, 8), (key2993, -18), (key2996, -6), (key3003, -6)]

def entry16_13 : Integer.Sparse Key := [(key2612, -24), (key2616, -12), (key2618, 36), (key2628, -12), (key2632, -24), (key2640, 54), (key2641, 36), (key2644, -6), (key2646, 18), (key2648, -30), (key2653, -36), (key2667, -36), (key2673, 36), (key2702, 72), (key2706, -24), (key2726, 54), (key2728, 72), (key2732, -6), (key2735, -36), (key2737, -36), (key2747, -72), (key2782, -12), (key2795, 36), (key2805, 72), (key2829, -16), (key2831, 72), (key2860, -6), (key2870, -6), (key2885, 12), (key2893, -30), (key2897, -36), (key2904, -54), (key2936, 18), (key2938, -30), (key2943, -36), (key2948, -20), (key2950, -36), (key2960, -64), (key2972, -30), (key2976, -36), (key2983, -54), (key2997, 60), (key2998, 72), (key3000, 84), (key3017, -8), (key3023, -18), (key3026, -18), (key3030, 60)]

def entry16_14 : Integer.Sparse Key := [(key2616, 36), (key2618, -12), (key2621, -24), (key2628, 12), (key2632, 24), (key2640, -30), (key2641, -24), (key2644, 6), (key2646, -42), (key2648, 30), (key2653, 24), (key2658, -12), (key2660, 12), (key2667, -24), (key2671, -12), (key2673, 24), (key2676, 12), (key2706, -24), (key2726, 30), (key2732, -6), (key2735, -72), (key2737, 72), (key2753, 12), (key2758, -12), (key2782, -12), (key2794, -36), (key2795, 24), (key2798, 36), (key2805, -12), (key2809, 12), (key2829, 64), (key2835, -60), (key2860, -54), (key2870, 54), (key2893, -54), (key2897, 72), (key2904, 18), (key2920, 36), (key2923, -36), (key2936, 42), (key2938, -30), (key2943, -24), (key2948, 44), (key2950, -48), (key2960, -8), (key2972, 54), (key2976, -72), (key2983, -18), (key3017, 8), (key3023, -18), (key3026, 18)]

def entry16_15 : Integer.Sparse Key := [(key2616, 36), (key2619, -36), (key2632, 36), (key2640, -72), (key2642, 36), (key2649, -36), (key2654, 36), (key2671, -36), (key2674, 36), (key2706, -36), (key2726, 72), (key2729, -36), (key2738, 36), (key2748, -36), (key2794, -108), (key2796, 108), (key2829, 108), (key2832, -108), (key2860, -108), (key2870, 108), (key2898, 108), (key2905, -108)]

def entry17_1 : Integer.Sparse Key := [(key706, -288), (key722, 288), (key860, 288), (key922, -288)]

def entry17_3 : Integer.Sparse Key := [(key2029, 288), (key2059, -288), (key2148, -288), (key2241, 288)]

def entry17_7 : Integer.Sparse Key := [(key2120, 288), (key2160, -576), (key2249, 288)]

def entry17_9 : Integer.Sparse Key := [(key779, 288), (key804, -576), (key873, 288)]

def entry17_14 : Integer.Sparse Key := [(key2063, -216), (key2069, -72), (key2092, 216), (key2095, 72), (key2152, 216), (key2166, 72), (key2194, -216), (key2200, -72), (key2246, 72), (key2253, -72), (key2305, -72), (key2310, 72)]

def entry17_15 : Integer.Sparse Key := [(key2063, -216), (key2069, -72), (key2079, 216), (key2085, 72), (key2152, 216), (key2166, 72), (key2176, -216), (key2187, -72), (key2246, 72), (key2253, -72), (key2279, -72), (key2287, 72)]

def entry17_16 : Integer.Sparse Key := [(key2032, -72), (key2037, 72), (key2062, -72), (key2072, 72), (key2078, 144), (key2082, -72), (key2087, -72), (key2151, 144), (key2169, 144), (key2175, -72), (key2179, -72), (key2189, -144), (key2275, -72), (key2281, -72), (key2289, -144), (key2328, 72), (key2330, 72), (key2333, 144)]

def entry18_0 : Integer.Sparse Key := [(key1976, -288), (key1981, 288), (key1983, 288), (key1997, -288)]

def entry18_1 : Integer.Sparse Key := [(key54, 96), (key56, 96), (key63, -288), (key122, -84), (key128, 96), (key198, -48), (key199, 84), (key693, 48), (key697, 48), (key845, -60), (key848, -96), (key854, 48), (key855, 60)]

def entry18_2 : Integer.Sparse Key := [(key1973, 144), (key1978, 144), (key1985, -288), (key2209, -144), (key2215, -144), (key2226, 144), (key2230, 144)]

def entry18_3 : Integer.Sparse Key := [(key2015, -288), (key2044, 144), (key2045, 144), (key2129, 144), (key2132, 144), (key2212, -144), (key2213, -144)]

def entry18_4 : Integer.Sparse Key := [(key694, 144), (key696, 144), (key699, -288), (key846, -144), (key847, -144), (key850, 144), (key852, 144)]

def entry18_5 : Integer.Sparse Key := [(key58, -96), (key65, 168), (key68, 96), (key82, -168), (key695, -192), (key698, 120), (key700, 192), (key712, -120)]

def entry18_6 : Integer.Sparse Key := [(key2013, 144), (key2019, 144), (key2026, -288), (key2042, -144), (key2047, -144), (key2055, 144), (key2056, 144)]

def entry18_7 : Integer.Sparse Key := [(key2103, -288), (key2108, 288), (key2109, 288), (key2131, -288)]

def entry18_8 : Integer.Sparse Key := [(key1974, 144), (key1977, 144), (key1982, -288), (key2210, -144), (key2214, -144), (key2219, 144), (key2223, 144)]

def entry18_9 : Integer.Sparse Key := [(key758, -288), (key762, 288), (key764, 288), (key789, -288)]

def entry18_10 : Integer.Sparse Key := [(key2014, 144), (key2018, 144), (key2023, -288), (key2043, -144), (key2046, -144), (key2051, 144), (key2052, 144)]

def entry18_11 : Integer.Sparse Key := [(key357, 144), (key359, 144), (key365, -288), (key527, -144), (key535, 144), (key674, -144), (key675, 144)]

def entry18_12 : Integer.Sparse Key := [(key1976, -288), (key1981, 144), (key1983, 144), (key2218, 144), (key2224, 144), (key2262, -144), (key2266, -144)]

def entry18_13 : Integer.Sparse Key := [(key2026, -288), (key2055, 144), (key2056, 144), (key2144, 144), (key2145, 144), (key2228, -144), (key2229, -144)]

def entry18_14 : Integer.Sparse Key := [(key2042, 144), (key2047, 144), (key2055, -144), (key2056, -144), (key2127, -144), (key2134, -144), (key2144, 144), (key2145, 144)]

def entry18_15 : Integer.Sparse Key := [(key2043, 144), (key2046, 144), (key2051, -144), (key2052, -144), (key2128, -144), (key2133, -144), (key2138, 144), (key2141, 144)]

def entry18_16 : Integer.Sparse Key := [(key2017, -288), (key2022, 144), (key2024, 144), (key2050, 144), (key2053, 144), (key2075, -144), (key2076, -144)]

def entry18_17 : Integer.Sparse Key := [(key783, -288), (key808, 288), (key837, 288), (key932, -288)]

def entry18_18 : Integer.Sparse Key := [(key757, 144), (key759, 144), (key761, -144), (key766, -160), (key768, -128), (key769, -144), (key793, 288)]

def entry19_1 : Integer.Sparse Key := [(key620, -288), (key624, 288), (key646, 288), (key652, -288)]

def entry19_3 : Integer.Sparse Key := [(key1959, 288), (key1961, -288), (key1967, -288), (key1970, 288)]

def entry19_7 : Integer.Sparse Key := [(key1963, 288), (key1965, -576), (key1968, 288)]

def entry19_9 : Integer.Sparse Key := [(key688, 288), (key689, -576), (key691, 288)]

def entry19_16 : Integer.Sparse Key := [(key1863, 288), (key1865, -288), (key1870, -288), (key1872, 288)]

def entry19_17 : Integer.Sparse Key := [(key536, 288), (key544, -576), (key556, 288)]

def entry19_18 : Integer.Sparse Key := [(key633, -288), (key635, 288), (key638, 288), (key644, -288)]

def entry20_1 : Integer.Sparse Key := [(key60, 40), (key62, -72), (key72, 152), (key125, -24), (key127, 96), (key135, -144), (key180, 16), (key704, -40), (key709, -216), (key723, 136), (key858, 24), (key863, 192), (key923, -144), (key940, -16)]

def entry20_2 : Integer.Sparse Key := [(key1993, -288), (key2008, 288), (key2238, 288), (key2301, -288)]

def entry20_3 : Integer.Sparse Key := [(key2030, 288), (key2060, -288), (key2149, -288), (key2242, 288)]

def entry20_4 : Integer.Sparse Key := [(key707, -288), (key716, 288), (key861, 288), (key893, -288)]

def entry20_7 : Integer.Sparse Key := [(key2121, 288), (key2161, -576), (key2250, 288)]

def entry20_8 : Integer.Sparse Key := [(key1991, -288), (key2001, 288), (key2236, 288), (key2270, -288)]

def entry20_9 : Integer.Sparse Key := [(key780, 288), (key805, -576), (key874, 288)]

def entry20_11 : Integer.Sparse Key := [(key364, -288), (key368, 288), (key534, 288), (key540, -288)]

def entry20_17 : Integer.Sparse Key := [(key777, 144), (key782, 144), (key802, -288), (key807, -144), (key812, -144), (key821, -144), (key824, 144), (key872, 144), (key877, 144), (key905, 144), (key907, -144)]

def entry20_18 : Integer.Sparse Key := [(key763, 48), (key765, 40), (key767, -48), (key773, -48), (key775, -40), (key785, -240), (key788, -24), (key790, -24), (key791, 72), (key792, 88), (key800, 24), (key810, 216), (key835, 24), (key838, 200), (key851, -96), (key933, -192)]

def entry20_19 : Integer.Sparse Key := [(key637, 288), (key643, -576), (key651, 288)]

def entry21_9 : Integer.Sparse Key := [(key2101, -288), (key2106, 288), (key2111, 288), (key2139, -288)]

def entry21_11 : Integer.Sparse Key := [(key1500, 144), (key1503, 144), (key1507, -288), (key1732, -144), (key1736, 144), (key1874, -144), (key1875, 144)]

def entry21_17 : Integer.Sparse Key := [(key2122, -288), (key2162, 288), (key2185, 288), (key2285, -288)]

def entry21_18 : Integer.Sparse Key := [(key2102, 144), (key2104, 144), (key2107, -144), (key2110, -144), (key2112, -144), (key2113, -144), (key2140, 288)]

def entry21_19 : Integer.Sparse Key := [(key1945, -288), (key1947, 288), (key1948, 288), (key1952, -288)]

def entry21_20 : Integer.Sparse Key := [(key2123, -288), (key2163, 288), (key2186, 288), (key2286, -288)]

end MUB6.Certificate.GramEntries.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13593 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13594 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13595 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13596 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13597 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13598 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13602 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13603 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13604 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13605 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13606 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13607 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2843, -2), (key2880, -2), (key2887, -2), (key2889, 4), (key2910, 2), (key2966, 4), (key2968, -2), (key2989, 2), (key2995, -2), (key3002, -2)]

def row13608 : Integer.Sparse Key := [(key2390, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2929, 4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13609 : Integer.Sparse Key := [(key2390, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2929, 4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13610 : Integer.Sparse Key := [(key2437, 4), (key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13611 : Integer.Sparse Key := [(key2437, 4), (key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4), (key3002, 4)]

def row13612 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2580, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4)]

def row13613 : Integer.Sparse Key := [(key2390, 4), (key2437, 4), (key2580, 4), (key2587, -4), (key2593, 4), (key2600, -4), (key2766, -4), (key2772, 4), (key2880, 4), (key2910, -4), (key2931, -4), (key2989, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14205 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14206 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14207 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14208 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14209 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14210 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14211 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14212 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14213 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14214 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14215 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14216 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14217 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14218 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14219 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2472, -2), (key2480, -2), (key2482, 4), (key2503, 4), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row14220 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14221 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14222 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14223 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14224 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14225 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2538, 4), (key2543, -4), (key2554, -4), (key2563, 4)]

def row14226 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14227 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14228 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14229 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14230 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14231 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14232 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14233 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14234 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2472, -4), (key2480, 8), (key2482, -4), (key2503, -4), (key2506, 8), (key2522, -4)]

def row14235 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14236 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14237 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14238 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14239 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

def row14240 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, 4), (key2480, -2), (key2482, -2), (key2503, -2), (key2506, -2), (key2522, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14349 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14350 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14351 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14352 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14353 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14354 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14355 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14356 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14357 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14358 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14359 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14360 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14361 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14362 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14363 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -2), (key1032, 4), (key1068, -2), (key1110, -4), (key1120, 4), (key1196, -2), (key1209, 2)]

def row14364 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14365 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14366 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14367 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14368 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14369 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -4), (key1110, 12), (key1120, -4), (key1147, -4), (key1189, -4), (key1196, 2), (key1209, 2)]

def row14370 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14371 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14372 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14373 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14374 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14375 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14376 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14377 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14378 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1110, 4), (key1120, -4), (key1147, 4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row14379 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14380 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14381 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14382 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14383 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14384 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, -2), (key1068, 2), (key1106, 4), (key1110, -4), (key1189, 4), (key1196, -2), (key1209, -2)]

def row14421 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14422 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14423 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14424 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14425 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14426 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14427 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14428 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14429 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14430 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14431 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14432 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14433 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14434 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14435 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2779, 2), (key2783, -1), (key2791, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row14436 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14437 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14438 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14439 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14440 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14441 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2937, -2), (key2942, 2), (key2949, -2), (key2959, 2), (key2973, 4), (key2975, -2), (key2982, -2)]

def row14442 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14443 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14444 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14445 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14446 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14447 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14448 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14449 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14450 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, -2), (key2867, 4), (key2894, -2), (key2896, 4), (key2903, -2)]

def row14451 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14452 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14453 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14454 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14455 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row14456 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, -1), (key2806, -1), (key2826, 2), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, 2), (key2896, -1), (key2903, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14529 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14530 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14531 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14532 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14533 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14534 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14535 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14536 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14537 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14538 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14539 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14540 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14541 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14542 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14543 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

def row14544 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14545 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14546 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14547 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14548 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14549 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

def row14550 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14551 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14552 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14553 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14554 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14555 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14556 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14557 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14558 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

def row14559 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14560 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14561 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14562 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14563 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14564 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

def row14565 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14566 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14567 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14568 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14569 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14570 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

def row14571 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

def row14572 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

def row14573 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

def row14574 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14575 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14576 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14577 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14578 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14579 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

def row14580 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14581 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14582 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 4), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14583 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 4), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14584 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14585 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

def row14586 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14587 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14588 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14589 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14590 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

def row14591 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14592 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

def row14593 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

def row14594 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2781, 4), (key2790, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2866, 4), (key2892, -2), (key2895, 4), (key2902, -2)]

def row14595 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14596 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14597 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14598 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14599 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14600 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 2), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, -1), (key2866, -1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row14621 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14622 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14623 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14624 : Integer.Sparse Key := [(key220, 6), (key225, -6), (key492, -6), (key497, 12), (key551, -6), (key664, -6), (key681, 6)]

def row14625 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14626 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14627 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14628 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14629 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14630 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14631 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14632 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14633 : Integer.Sparse Key := [(key220, 2), (key225, -2), (key492, -2), (key497, 4), (key551, -2), (key664, -2), (key681, 2)]

def row14634 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14635 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14636 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14637 : Integer.Sparse Key := [(key220, 6), (key225, -6), (key492, -6), (key497, 12), (key551, -6), (key664, -6), (key681, 6)]

def row14638 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14639 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14640 : Integer.Sparse Key := [(key220, -2), (key225, 2), (key492, 2), (key497, -4), (key551, 2), (key664, 2), (key681, -2)]

def row14661 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14662 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14663 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14664 : Integer.Sparse Key := [(key1360, -6), (key1372, 6), (key1486, -6), (key1511, 6), (key1712, 12), (key1721, -6), (key1739, -6)]

def row14665 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14666 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14667 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14668 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14669 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14670 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14671 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14672 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14673 : Integer.Sparse Key := [(key1360, -2), (key1372, 2), (key1486, -2), (key1511, 2), (key1712, 4), (key1721, -2), (key1739, -2)]

def row14674 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14675 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14676 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14677 : Integer.Sparse Key := [(key1360, -6), (key1372, 6), (key1486, -6), (key1511, 6), (key1712, 12), (key1721, -6), (key1739, -6)]

def row14678 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14679 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

def row14680 : Integer.Sparse Key := [(key1360, 2), (key1372, -2), (key1486, 2), (key1511, -2), (key1712, -4), (key1721, 2), (key1739, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14741 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14742 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14743 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14744 : Integer.Sparse Key := [(key1501, -12), (key1506, 12), (key1733, 12), (key1735, -12)]

def row14745 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14746 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14747 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14748 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14749 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14750 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14751 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14752 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14753 : Integer.Sparse Key := [(key1501, -4), (key1506, 4), (key1733, 4), (key1735, -4)]

def row14754 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14755 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14756 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14757 : Integer.Sparse Key := [(key1501, -12), (key1506, 12), (key1733, 12), (key1735, -12)]

def row14758 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14759 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14760 : Integer.Sparse Key := [(key1501, 4), (key1506, -4), (key1733, -4), (key1735, 4)]

def row14781 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14782 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14783 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14784 : Integer.Sparse Key := [(key358, -12), (key363, 12), (key528, 12), (key532, -12)]

def row14785 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14786 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14787 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14788 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14789 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14790 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14791 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14792 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14793 : Integer.Sparse Key := [(key358, -4), (key363, 4), (key528, 4), (key532, -4)]

def row14794 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14795 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14796 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14797 : Integer.Sparse Key := [(key358, -12), (key363, 12), (key528, 12), (key532, -12)]

def row14798 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14799 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14800 : Integer.Sparse Key := [(key358, 4), (key363, -4), (key528, -4), (key532, 4)]

def row14841 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14842 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14843 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14844 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

def row14845 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

def row14846 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -4), (key2525, 4), (key2532, 4), (key2533, -4), (key2562, 4), (key2564, -4)]

def row14847 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14848 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14849 : Integer.Sparse Key := [(key2457, 4), (key2460, -4), (key2521, 4), (key2525, -4), (key2532, -4), (key2533, 4), (key2562, -4), (key2564, 4)]

def row14850 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

def row14851 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

def row14852 : Integer.Sparse Key := [(key2457, -4), (key2460, 4), (key2521, -8), (key2525, -4), (key2532, 8), (key2533, 4), (key2562, 4), (key2564, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row14988 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

def row14989 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

def row14990 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

def row14991 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

def row14992 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

def row14993 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

def row14994 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

def row14995 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

def row14996 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

def row14997 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row14998 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row14999 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15000 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15001 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15002 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row15003 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

def row15004 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

def row15005 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

def row15006 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15007 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15008 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15009 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15010 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15011 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

def row15012 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

def row15013 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

def row15014 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

def row15069 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15070 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15071 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15072 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15073 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15074 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15075 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15076 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15077 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

def row15078 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15079 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15080 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15081 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15082 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15083 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15084 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15085 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15086 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

def row15087 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15088 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15089 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15090 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15091 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15092 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

def row15093 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

def row15094 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

def row15095 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

def row15096 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15097 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15098 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15099 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15100 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15101 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15102 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15103 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15104 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

def row15105 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15106 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15107 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15108 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15109 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15110 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15111 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15112 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15113 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

def row15114 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15115 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15116 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15117 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15118 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15119 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

def row15120 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

def row15121 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

def row15122 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

def row15150 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

def row15151 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

def row15152 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

def row15153 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

def row15154 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

def row15155 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

def row15156 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

def row15157 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

def row15158 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

def row15165 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

def row15166 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

def row15167 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

def row15177 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15178 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15179 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15180 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15181 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15182 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15183 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15184 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15185 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15186 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15187 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15188 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

def row15189 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15190 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15191 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15192 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15193 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

def row15194 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15411 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15412 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15413 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15414 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15415 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15416 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15417 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15418 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15419 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15420 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15421 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15422 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2802, -2), (key2806, -2), (key2826, -2), (key2852, 4), (key2857, 4), (key2867, 4), (key2894, -2), (key2896, -2), (key2903, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, -2)]

def row15423 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15424 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15425 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15426 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15427 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15428 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15429 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15430 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15431 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15432 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15433 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15434 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 2), (key2806, -1), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, -1), (key2896, 2), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, -1), (key2982, 1)]

def row15435 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15436 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15437 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15438 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15439 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15440 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2699, 2), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, -1), (key2802, -1), (key2806, 2), (key2826, 1), (key2852, -1), (key2857, -1), (key2867, -2), (key2894, 2), (key2896, -1), (key2903, 1), (key2949, -1), (key2959, -1), (key2973, -1), (key2975, 2), (key2982, 1)]

def row15441 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15442 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15443 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15444 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15445 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15446 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2723, -2), (key2746, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2826, -2), (key2867, 4), (key2903, -2), (key2937, -2), (key2942, 2), (key2959, 2), (key2982, -2)]

def row15483 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15484 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15485 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, -2), (key2394, -4), (key2766, 4), (key2772, 2), (key2887, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -4), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15486 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15487 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15488 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15489 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15490 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15491 : Integer.Sparse Key := [(key2383, -2), (key2390, 2), (key2766, -1), (key2772, -1), (key2843, 1), (key2880, -1), (key2887, 2), (key2889, 1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -3), (key2968, 2), (key2989, 3), (key2995, -3), (key3002, -1)]

def row15492 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15493 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15494 : Integer.Sparse Key := [(key2406, 4), (key2411, 2), (key2437, -2), (key2443, -4), (key2587, 4), (key2593, 2), (key2598, -2), (key2600, -4), (key2887, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2995, 8), (key3002, 4)]

def row15495 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15496 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15497 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15498 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15499 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15500 : Integer.Sparse Key := [(key2411, -2), (key2437, 2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2843, 1), (key2880, -1), (key2887, -3), (key2889, 2), (key2910, 3), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -3), (key3002, -1)]

def row15501 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15502 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15503 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15504 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7586 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7587 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7588 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7589 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7590 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7591 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2929, 2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7592 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7593 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7594 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7595 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7596 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7597 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2593, -2), (key2598, 2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 2), (key2889, -2), (key2931, -2), (key2966, 2), (key2968, -2), (key2995, 2), (key3002, 2)]

def row7598 : Integer.Sparse Key := [(key2390, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2929, 2), (key2968, -2), (key3002, 2)]

def row7599 : Integer.Sparse Key := [(key2390, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2929, 2), (key2968, -2), (key3002, 2)]

def row7600 : Integer.Sparse Key := [(key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2598, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key3002, 2)]

def row7601 : Integer.Sparse Key := [(key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2593, -2), (key2598, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2), (key3002, 2)]

def row7602 : Integer.Sparse Key := [(key2390, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2580, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2)]

def row7603 : Integer.Sparse Key := [(key2390, 2), (key2437, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2580, 2), (key2593, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2968, -2)]

def row7604 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7605 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7606 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7607 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7608 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row7609 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2480, 2), (key2503, 2), (key2524, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7754 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7755 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7756 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7757 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7758 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7759 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -8), (key2851, 2), (key2858, 2), (key2868, 2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7760 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -8), (key2851, 2), (key2858, 2), (key2868, 2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7761 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7762 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -6), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -2), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7763 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7764 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7765 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2801, -4), (key2807, -4), (key2827, -4), (key2851, 2), (key2858, 2), (key2868, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row7766 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7767 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7768 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7769 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7770 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7771 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7772 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7773 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7774 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7775 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7776 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7777 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2752, 2), (key2757, 2), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7778 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7779 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7780 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 2), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7781 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 2), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7782 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7783 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2757, 1), (key2778, 1), (key2792, 2), (key2801, 1), (key2827, 2), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7784 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7785 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7786 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7787 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7788 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row7789 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2698, -1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2851, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7825 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7826 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7827 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7828 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7829 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7830 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7831 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7832 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7833 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7834 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7835 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7836 : Integer.Sparse Key := [(key2766, 4), (key2772, 2), (key2843, 4), (key2880, 2), (key2887, 4), (key2889, 4), (key2910, 4), (key2929, -2), (key2931, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, -4), (key3002, -2)]

def row7885 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7886 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7887 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7888 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7889 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7890 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7891 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7892 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7893 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7894 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7895 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7896 : Integer.Sparse Key := [(key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2922, 2)]

def row7921 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7922 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7923 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7924 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7925 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7926 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -8), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7927 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -8), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7928 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7929 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -6), (key2657, -2), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7930 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7931 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7932 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, -4), (key2630, -4), (key2638, -4), (key2657, -4), (key2659, -2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2)]

def row7933 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7934 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7935 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7936 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7937 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7938 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 8), (key3016, 2)]

def row7939 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 8), (key3016, 2)]

def row7940 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7941 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

def row7942 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7943 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7944 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

def row7945 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7946 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7947 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7948 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7949 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7950 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7951 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7952 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7953 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7954 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7955 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7956 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

def row7957 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7958 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7959 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7960 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7961 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7962 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7963 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7964 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7965 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7966 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7967 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7968 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7969 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7970 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7971 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7972 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7973 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7974 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7975 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7976 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7977 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7978 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7979 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

def row7980 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8197 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8198 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8199 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8200 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8201 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8202 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8203 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8204 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8205 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8206 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8207 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8208 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

def row8269 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8270 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8271 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8272 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8273 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8274 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8275 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8276 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8277 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8278 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8279 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

def row8280 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8329 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8330 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8331 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8332 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8333 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8334 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8335 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8336 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8337 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8338 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8339 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8340 : Integer.Sparse Key := [(key2614, 2), (key2630, 2), (key2638, 2), (key2657, -4), (key2659, -2), (key2669, 2), (key2704, 2), (key2724, 2), (key2752, -4), (key2757, -2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key2918, -4), (key2919, -4), (key2922, -4)]

def row8377 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8378 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8379 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8380 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8381 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8382 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8383 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8384 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8385 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8386 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8387 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8388 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8389 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8390 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8391 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8392 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8393 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8394 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8395 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8396 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8397 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8398 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8399 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8400 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2918, -2), (key2919, -2), (key2922, -2), (key3021, 2), (key3022, 2), (key3025, 2)]

def row8401 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8402 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8403 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8404 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8405 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8406 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8407 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8408 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8409 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8410 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8411 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

def row8412 : Integer.Sparse Key := [(key2657, 4), (key2659, 2), (key2752, 4), (key2757, 2), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, -4), (key3009, -2), (key3011, -4), (key3016, -2), (key3021, -4), (key3022, -4), (key3025, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8449 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8450 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8451 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8452 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8453 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8454 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8455 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8460 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2752, 2), (key2757, 2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8461 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8462 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8463 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 2), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8464 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 2), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8465 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8466 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2757, 1), (key2778, 1), (key2784, -2), (key2801, 1), (key2807, -2), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3009, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8467 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8468 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8469 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8470 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8471 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8472 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, -2), (key2792, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -2), (key2868, -2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, 1)]

def row8473 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8474 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8475 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8476 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8477 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8478 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -8), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8479 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8480 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8481 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -6), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8482 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -6), (key2704, 2), (key2724, 2), (key2778, -2), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8483 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

def row8484 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, -4), (key2630, 2), (key2638, 2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2724, 2), (key2778, -4), (key2784, 2), (key2792, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, -4), (key2858, 2), (key2868, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1002 : Sparse Master := [(Sum.inr 1002, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


