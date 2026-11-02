-- Prove2me | Definitions.Def_OAIQ106D083
-- name    : OAIQ106D083
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:53:07.41039+00:00
-- url     : https://prove2.me/theorems/047c582d-f124-4c3c-80d9-34f1bafd8e4e
-- title:
--   Definitions bundle OAIQ106D083 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 718 declarations of OpenAI's Lean: 718 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entry11_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_12`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entry12_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_12`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_13`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entry13_4` and 678 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block1Data`, `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block20`, `MutuallyUnbiased_GramKeys_Block21`, `MutuallyUnbiased_GramKeys_Block22`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block24`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block10`, `MutuallyUnbiased_GramRows_Block11`, `MutuallyUnbiased_GramRows_Block12`, `MutuallyUnbiased_GramRows_Block13`, `MutuallyUnbiased_GramRows_Block14`, `MutuallyUnbiased_GramRows_Block15`, `MutuallyUnbiased_GramRows_Block16`, `MutuallyUnbiased_GramRows_Block17`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block6`, `MutuallyUnbiased_GramRows_Block7`, `MutuallyUnbiased_GramRows_Block8`, `MutuallyUnbiased_GramRows_Block9`, `MutuallyUnbiased_MixedSemantics_Values18`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D143`, `OAIQ106D144`, `OAIQ106D145`, `OAIQ106D146`, `OAIQ106D147`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D155`, `OAIQ106D156`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D162`, `OAIQ106D163`, `OAIQ106D164`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D168`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172`, `OAIQ106D173`, `OAIQ106D174`, `OAIQ106D175`, `OAIQ106D176`, `OAIQ106D177`, `OAIQ106D178`, `OAIQ106D179`, `OAIQ106D180`, `OAIQ106D181`, `OAIQ106D183`, `OAIQ106D184`, `OAIQ106D185` and `OAIQ106D186`.
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

def key2 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key4 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key6 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key17 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key28 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key42 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key69 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key74 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key85 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key108 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩

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

def key132 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key148 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, -3), (2, 2)]⟩
def key150 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩
def key164 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 0), (2, 2)]⟩
def key166 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key184 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, -3), (2, 2)]⟩
def key186 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key211 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key216 : Key := ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key238 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key241 : Key := ⟨0, 0, [(-2, -2), (-1, -1), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key250 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key253 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 1), (2, 0)]⟩

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

def key1293 : Key := ⟨0, 1, [(-2, -2), (-1, -1), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key1313 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key1319 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key1335 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (0, 1), (3, 1)]⟩
def key1337 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key1388 : Key := ⟨0, 1, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key1405 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩

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

def key1410 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key1421 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 3), (2, 0)]⟩
def key1432 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 2), (3, 1)]⟩
def key1433 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 2)]⟩
def key1439 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key1455 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -2), (0, 0), (1, 1), (2, 1)]⟩
def key1475 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (0, 0), (3, 1)]⟩
def key1477 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key1479 : Key := ⟨0, 1, [(-2, -1), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1543 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key1553 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key1570 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -2), (0, 0), (1, 3), (2, 0)]⟩
def key1581 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 2), (3, 1)]⟩
def key1588 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key1590 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key1621 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 3), (2, -1)]⟩
def key1630 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -2)]⟩
def key1655 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -2), (0, -1), (1, 1), (2, 1)]⟩

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

def key1686 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (0, -1), (3, 1)]⟩
def key1688 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (1, 1), (2, -1)]⟩
def key1770 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, -1), (0, 0), (0, 1), (3, 1)]⟩

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

def key1845 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key1906 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 1)]⟩
def key1910 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩

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

def key1923 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 1)]⟩
def key1925 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (1, 1), (2, -1)]⟩

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

def key263 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key277 : Key := ⟨0, 0, [(-2, -2), (-1, 2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key278 : Key := ⟨0, 0, [(-2, -2), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key304 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key307 : Key := ⟨0, 0, [(-2, -1), (-1, -2), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key318 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 0), (1, 3), (2, 0)]⟩
def key321 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -2), (0, 2), (1, 1), (2, 0)]⟩
def key331 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key346 : Key := ⟨0, 0, [(-2, -1), (-1, 2), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key347 : Key := ⟨0, 0, [(-2, -1), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key376 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key380 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩

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

def key2639 : Key := ⟨1, 1, [(-2, -2), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key2656 : Key := ⟨1, 1, [(-2, -2), (-1, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key2686 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (1, 0), (1, 1), (1, 2)]⟩

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

def key2695 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key2725 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key2751 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2915 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key2921 : Key := ⟨1, 1, [(-2, 0), (-1, 2), (0, -1), (0, -1), (1, 1), (2, -1)]⟩

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

def key2946 : Key := ⟨1, 1, [(-2, 1), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key2999 : Key := ⟨1, 1, [(-2, 1), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key3013 : Key := ⟨1, 1, [(-2, 2), (-1, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key3024 : Key := ⟨1, 1, [(-2, 2), (-1, 0), (0, -1), (0, -1), (1, 1), (2, -1)]⟩
def key3051 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 1), (2, 1)]⟩
def key3057 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 1), (1, 1), (2, 0)]⟩
def key3063 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, 0)]⟩
def key3065 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -1)]⟩

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

def key3081 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (1, 1), (2, 2)]⟩
def key3083 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 2), (1, 1), (2, 0)]⟩
def key3086 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 1), (2, 2)]⟩
def key3089 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 2), (1, 1), (2, -1)]⟩
def key3092 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 2), (0, -1), (1, 1), (2, 0)]⟩
def key3093 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 2), (0, 0), (1, 1), (2, -1)]⟩
def key3098 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, 0)]⟩
def key3102 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 0), (1, 3), (2, -2)]⟩
def key3105 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 2), (1, 1), (2, -2)]⟩
def key3116 : Key := ⟨1, 1, [(-1, -1), (-1, 1), (-1, 1), (0, -2), (1, 1), (2, 0)]⟩
def key3124 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (1, 3), (2, -1)]⟩
def key3126 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -1), (1, 3), (2, -2)]⟩
def key3142 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -2), (1, 1), (2, -1)]⟩
def key3143 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -2)]⟩

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

def key390 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key400 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key411 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -2), (0, 2), (1, 1), (2, 0)]⟩
def key421 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -2)]⟩
def key427 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 1)]⟩
def key445 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 2), (1, 1), (2, -1)]⟩
def key453 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 2), (1, 1), (2, -2)]⟩
def key459 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 2), (2, -3)]⟩
def key460 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 2), (1, 1), (2, -3)]⟩
def key465 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 2), (2, 0)]⟩
def key482 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key486 : Key := ⟨0, 0, [(-2, 0), (-1, 2), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key487 : Key := ⟨0, 0, [(-2, 0), (-1, 2), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key488 : Key := ⟨0, 0, [(-2, 0), (-1, 2), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key489 : Key := ⟨0, 0, [(-2, 0), (-1, 2), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key490 : Key := ⟨0, 0, [(-2, 0), (-1, 2), (0, 0), (0, 0), (1, 1), (2, -3)]⟩

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

def key566 : Key := ⟨0, 0, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key591 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 2), (2, 0)]⟩

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

def key654 : Key := ⟨0, 0, [(-2, 2), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 0)]⟩
def key656 : Key := ⟨0, 0, [(-2, 2), (-1, -2), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key657 : Key := ⟨0, 0, [(-2, 2), (-1, -1), (0, -2), (0, 0), (1, 1), (2, 0)]⟩
def key658 : Key := ⟨0, 0, [(-2, 2), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -2)]⟩
def key659 : Key := ⟨0, 0, [(-2, 2), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key660 : Key := ⟨0, 0, [(-2, 2), (-1, 0), (0, -2), (0, -1), (1, 1), (2, 0)]⟩
def key661 : Key := ⟨0, 0, [(-2, 2), (-1, 0), (0, -2), (0, 0), (1, 1), (2, -1)]⟩
def key662 : Key := ⟨0, 0, [(-2, 2), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -2)]⟩
def key663 : Key := ⟨0, 0, [(-2, 2), (-1, 0), (0, 0), (0, 0), (1, 1), (2, -3)]⟩

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

def key992 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key998 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key1000 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 2), (1, 0), (2, 1)]⟩
def key1010 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key1014 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (0, 2), (1, -1), (2, 1)]⟩

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

def key1027 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key1048 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 1), (2, 2)]⟩
def key1049 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key1053 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 0), (2, 1)]⟩
def key1054 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key1066 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key1070 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (0, 2), (1, -2), (2, 1)]⟩
def key1118 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key1134 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩
def key1135 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩
def key1141 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, -1), (2, 1)]⟩
def key1142 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 2), (1, 1), (2, -1)]⟩
def key1145 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 0), (1, -2), (2, 3)]⟩
def key1149 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (0, 2), (1, -2), (2, 1)]⟩

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

def key1192 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 1), (1, 0), (2, 1)]⟩
def key1198 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (0, 1), (1, -1), (2, 1)]⟩
def key1211 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 1), (1, -2), (2, 1)]⟩
def key1212 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (0, 1), (1, 1), (2, -2)]⟩
def key1237 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 0), (2, 1)]⟩
def key1238 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key1239 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, -1), (2, 1)]⟩
def key1240 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization

def entry1_0 : Integer.Sparse Key := [(key1422, 120), (key1453, -120), (key1571, -120), (key1653, 120), (key1786, 120), (key1811, -120)]

def entry1_1 : Integer.Sparse Key := [(key234, 120), (key246, -120), (key300, -120), (key314, 144), (key383, 96), (key404, -120)]

def entry2_0 : Integer.Sparse Key := [(key2616, 12), (key2618, -12), (key2632, -12), (key2640, 6), (key2641, 12), (key2644, 6), (key2646, -6), (key2648, 6), (key2653, -12), (key2667, -12), (key2673, 12), (key2702, 72), (key2706, 12), (key2726, -6), (key2728, 48), (key2732, -6), (key2735, -60), (key2737, -12), (key2747, -48), (key2795, -12), (key2805, -72), (key2829, 16), (key2831, -48), (key2860, 18), (key2870, -18), (key2893, 42), (key2897, 12), (key2904, 30), (key2936, 6), (key2938, -6), (key2943, 12), (key2948, 44), (key2950, 12), (key2960, 40), (key2972, -42), (key2976, -12), (key2983, -30), (key3017, 8), (key3023, 18), (key3026, -18)]

def entry2_1 : Integer.Sparse Key := [(key1289, 120), (key1309, -120), (key1384, -120), (key1417, 120), (key1539, 120), (key1566, -120)]

def entry2_2 : Integer.Sparse Key := [(key2608, 48), (key2614, 72), (key2624, -48), (key2630, -60), (key2638, -32), (key2657, 8), (key2659, 12), (key2663, -48), (key2669, -72), (key2698, 60), (key2704, 84), (key2724, 24), (key2757, -24), (key2778, 36), (key2784, 36), (key2792, 24), (key2801, -48), (key2807, -60), (key2827, -32), (key2919, -12), (key2922, 12), (key3011, 8), (key3016, 12), (key3022, 12), (key3025, -12)]

def entry3_0 : Integer.Sparse Key := [(key1033, 120), (key1041, -120), (key1111, -120), (key1127, 120), (key1193, 120), (key1199, -120)]

def entry3_1 : Integer.Sparse Key := [(key20, 120), (key31, -120), (key45, -120), (key70, 120), (key111, 120), (key133, -120)]

def entry3_2 : Integer.Sparse Key := [(key1001, 120), (key1015, -120), (key1036, -120), (key1071, 120), (key1123, 120), (key1150, -120)]

def entry4_0 : Integer.Sparse Key := [(key2785, 120), (key2793, -120), (key2808, -120), (key2828, 120), (key2859, 120), (key2869, -120)]

def entry4_1 : Integer.Sparse Key := [(key1287, 120), (key1307, -120), (key1382, -120), (key1415, 120), (key1537, 120), (key1564, -120)]

def entry4_2 : Integer.Sparse Key := [(key2610, 120), (key2626, -120), (key2665, -120), (key2700, 120), (key2780, 120), (key2803, -120)]

def entry4_3 : Integer.Sparse Key := [(key995, 120), (key1011, -120), (key1030, -120), (key1067, 120), (key1119, 120), (key1146, -120)]

def entry4_4 : Integer.Sparse Key := [(key2606, 120), (key2622, -120), (key2661, -120), (key2696, 144), (key2776, 96), (key2799, -120)]

def entry5_0 : Integer.Sparse Key := [(key1296, 48), (key1303, -48), (key1316, -48), (key1330, 48), (key1340, 48), (key1346, -48), (key1391, 12), (key1398, -12), (key1424, -12), (key1448, 12), (key1458, 12), (key1467, -12), (key1546, -12), (key1560, 12), (key1573, 12), (key1597, -12), (key1660, -12), (key1668, 12), (key1775, 12), (key1781, -12), (key1788, 60), (key1791, -72), (key1799, 12), (key1813, -60), (key1818, 72), (key1826, -12), (key1840, 60), (key1842, -60)]

def entry5_1 : Integer.Sparse Key := [(key387, 120), (key396, -120), (key408, -120), (key417, 120), (key441, 120), (key449, -120)]

def entry5_2 : Integer.Sparse Key := [(key1291, 12), (key1299, -12), (key1311, -12), (key1327, 12), (key1352, 12), (key1355, -12), (key1386, -12), (key1394, 12), (key1419, 12), (key1445, -12), (key1473, -12), (key1481, 12), (key1541, 12), (key1549, 60), (key1557, -72), (key1568, -12), (key1576, -60), (key1594, 72), (key1625, 60), (key1634, -60), (key1684, 12), (key1690, -12), (key1897, 48), (key1900, -48), (key1904, -48), (key1912, 48), (key1921, 48), (key1927, -48)]

def entry5_4 : Integer.Sparse Key := [(key1543, 120), (key1553, -120), (key1570, -120), (key1590, 120), (key1621, 120), (key1630, -120)]

def entry5_5 : Integer.Sparse Key := [(key236, 48), (key241, -48), (key248, -48), (key263, 72), (key277, 24), (key278, -48), (key302, 12), (key307, -12), (key316, -32), (key321, 12), (key331, 24), (key347, -24), (key385, 8), (key390, -12), (key400, 24), (key406, 72), (key411, -60), (key421, -32), (key435, -60), (key445, 72), (key453, 12), (key487, 48), (key488, -72), (key657, 8), (key658, 12), (key660, -12), (key661, 24), (key662, -12)]

def entry6_1 : Integer.Sparse Key := [(key1432, 120), (key1475, -120), (key1581, -120), (key1686, 120), (key1906, 120), (key1923, -120)]

def entry6_2 : Integer.Sparse Key := [(key2679, -12), (key2691, -8), (key2710, 12), (key2717, 132), (key2754, -12), (key2755, -132), (key2813, -12), (key2820, -132), (key2921, 96), (key3013, 12), (key3014, 116), (key3024, -96), (key3047, 12), (key3058, 8), (key3061, -12), (key3068, 12), (key3075, -12), (key3076, 12), (key3096, 12), (key3105, -12), (key3113, 12), (key3115, 4), (key3142, 24), (key3143, -24)]

def entry6_3 : Integer.Sparse Key := [(key1048, 120), (key1054, -120), (key1134, -120), (key1142, 120), (key1238, 120), (key1240, -120)]

def entry6_4 : Integer.Sparse Key := [(key3063, 120), (key3065, -120), (key3098, -120), (key3102, 120), (key3124, 120), (key3126, -120)]

def entry6_5 : Integer.Sparse Key := [(key1405, 120), (key1410, -120), (key1433, -120), (key1439, 120), (key1477, 120), (key1479, -120)]

def entry6_6 : Integer.Sparse Key := [(key3081, 120), (key3083, -120), (key3086, -120), (key3089, 144), (key3092, 96), (key3093, -120)]

def entry7_0 : Integer.Sparse Key := [(key1296, 12), (key1303, -12), (key1316, -12), (key1330, 12), (key1340, 12), (key1346, -12), (key1391, -12), (key1398, 12), (key1424, 72), (key1448, 48), (key1455, -60), (key1458, -12), (key1467, -48), (key1546, 12), (key1560, -12), (key1573, -72), (key1597, -48), (key1655, 60), (key1660, 12), (key1668, 48), (key1775, -12), (key1781, 12), (key1788, 60), (key1791, 12), (key1799, 48), (key1813, -60), (key1818, -12), (key1826, -48)]

def entry7_1 : Integer.Sparse Key := [(key238, 120), (key250, -120), (key304, -120), (key318, 120), (key387, 120), (key408, -120)]

def entry7_2 : Integer.Sparse Key := [(key1291, 48), (key1299, 72), (key1311, -48), (key1319, -60), (key1327, -12), (key1352, -12), (key1355, 12), (key1386, -48), (key1394, -72), (key1419, 48), (key1427, 60), (key1445, 12), (key1473, 12), (key1481, -12), (key1541, 48), (key1549, 60), (key1557, 12), (key1568, -48), (key1576, -60), (key1594, -12), (key1684, -12), (key1690, 12), (key1897, 12), (key1900, -12), (key1904, -12), (key1912, 12), (key1921, 12), (key1927, -12)]

def entry7_4 : Integer.Sparse Key := [(key1293, 120), (key1313, -120), (key1388, -120), (key1421, 120), (key1543, 120), (key1570, -120)]

def entry7_5 : Integer.Sparse Key := [(key236, 12), (key241, -12), (key248, -12), (key263, 24), (key278, -12), (key302, -12), (key307, 12), (key316, 18), (key321, 66), (key331, 36), (key346, -72), (key347, -48), (key385, 6), (key390, -6), (key400, -12), (key406, -12), (key411, -60), (key421, -44), (key445, 18), (key453, -18), (key487, 42), (key488, 12), (key489, 30), (key656, 12), (key657, 68), (key658, 48), (key660, -42), (key661, 6), (key662, -48)]

def entry7_6 : Integer.Sparse Key := [(key1439, 120), (key1479, -120), (key1588, -120), (key1688, 120), (key1910, 120), (key1925, -120)]

def entry7_7 : Integer.Sparse Key := [(key236, 48), (key241, 72), (key248, -48), (key253, -60), (key263, -32), (key277, 8), (key278, 12), (key302, -48), (key307, -72), (key316, 60), (key321, 84), (key331, 24), (key347, -24), (key385, 36), (key390, 36), (key400, 24), (key406, -48), (key411, -60), (key421, -32), (key488, -12), (key489, 12), (key657, 8), (key658, 12), (key661, 12), (key662, -12)]

def entry8_0 : Integer.Sparse Key := [(key1033, 120), (key1040, -120), (key1111, -120), (key1126, 120), (key1192, 120), (key1198, -120)]

def entry8_1 : Integer.Sparse Key := [(key17, 120), (key28, -120), (key42, -120), (key69, 120), (key108, 120), (key132, -120)]

def entry8_2 : Integer.Sparse Key := [(key1000, 120), (key1014, -120), (key1035, -120), (key1070, 120), (key1122, 120), (key1149, -120)]

def entry8_3 : Integer.Sparse Key := [(key2, 120), (key6, -120), (key85, -120), (key150, 120), (key166, 120), (key186, -120)]

def entry8_4 : Integer.Sparse Key := [(key992, 120), (key1010, -120), (key1027, -120), (key1066, 120), (key1118, 120), (key1145, -120)]

def entry8_5 : Integer.Sparse Key := [(key376, 120), (key380, -120), (key427, -120), (key459, 120), (key465, 120), (key482, -120)]

def entry8_6 : Integer.Sparse Key := [(key1049, 120), (key1053, -120), (key1135, -120), (key1141, 120), (key1237, 120), (key1239, -120)]

def entry8_7 : Integer.Sparse Key := [(key211, 120), (key216, -120), (key380, -120), (key465, 120), (key566, 120), (key591, -120)]

def entry8_8 : Integer.Sparse Key := [(key1, 120), (key4, -120), (key84, -120), (key148, 192), (key164, 48), (key184, -120)]

def entry9_0 : Integer.Sparse Key := [(key2617, 12), (key2620, -12), (key2633, -12), (key2643, 18), (key2650, 6), (key2655, -12), (key2672, 48), (key2675, -48), (key2707, -12), (key2730, 18), (key2739, 18), (key2749, 46), (key2751, -42), (key2787, -24), (key2797, 18), (key2810, -12), (key2833, 18), (key2899, 12), (key2906, -42), (key2915, 42), (key2940, 18), (key2945, -22), (key2946, -18), (key2952, 6), (key2962, -12), (key2978, -42), (key2985, 12), (key2994, 42), (key2999, 18), (key3001, 18), (key3004, -60)]

def entry9_1 : Integer.Sparse Key := [(key1314, 120), (key1335, -120), (key1544, -120), (key1653, 120), (key1770, 120), (key1811, -120)]

def entry9_2 : Integer.Sparse Key := [(key2616, -12), (key2618, 12), (key2628, 72), (key2640, -16), (key2641, 48), (key2646, -44), (key2648, -12), (key2653, -40), (key2660, -8), (key2667, -6), (key2671, 18), (key2673, -6), (key2676, -6), (key2706, -30), (key2726, 36), (key2728, 12), (key2732, 6), (key2735, -6), (key2737, 6), (key2747, -12), (key2753, -18), (key2758, 30), (key2782, -42), (key2786, -12), (key2794, 6), (key2795, -30), (key2798, 6), (key2809, 12), (key2829, -6), (key2831, -12), (key2835, -6), (key2860, 18), (key2870, -18), (key2893, 42), (key2897, 30), (key2904, 12), (key2920, 18), (key2923, -18), (key2936, 24), (key2938, 6), (key2943, 18), (key2948, 6), (key2950, -6), (key2960, 12), (key2972, -42), (key2976, -30), (key2983, -12)]

def entry9_3 : Integer.Sparse Key := [(key998, 120), (key1006, -120), (key1111, -120), (key1155, 120), (key1193, 120), (key1212, -120)]

def entry9_4 : Integer.Sparse Key := [(key2631, 120), (key2639, -120), (key2705, -120), (key2725, 120), (key2859, 120), (key2869, -120)]

def entry9_5 : Integer.Sparse Key := [(key1296, 12), (key1303, -12), (key1316, -12), (key1330, 12), (key1340, 12), (key1346, -12), (key1391, 48), (key1398, -48), (key1424, -48), (key1448, 48), (key1458, 48), (key1467, -48), (key1546, 12), (key1560, -12), (key1573, -12), (key1597, 12), (key1660, 12), (key1668, -12), (key1772, 60), (key1775, -72), (key1781, 12), (key1791, 12), (key1799, -12), (key1813, -60), (key1818, -12), (key1826, 72), (key1840, 60), (key1845, -60)]

def entry9_7 : Integer.Sparse Key := [(key1296, -12), (key1303, 12), (key1316, 72), (key1330, 48), (key1337, -60), (key1340, -12), (key1346, -48), (key1391, 12), (key1398, -12), (key1424, -12), (key1448, 12), (key1458, 12), (key1467, -12), (key1546, -72), (key1560, -48), (key1573, 12), (key1597, -12), (key1655, 60), (key1660, 48), (key1668, 12), (key1772, 60), (key1775, 12), (key1781, 48), (key1791, -12), (key1799, 12), (key1813, -60), (key1818, -48), (key1826, -12)]

def entry9_8 : Integer.Sparse Key := [(key998, 120), (key1005, -120), (key1111, -120), (key1154, 120), (key1192, 120), (key1211, -120)]

def entry9_9 : Integer.Sparse Key := [(key2617, 48), (key2620, -48), (key2633, 12), (key2643, -32), (key2650, 8), (key2655, 72), (key2656, -60), (key2672, 12), (key2675, -12), (key2730, 12), (key2749, 16), (key2787, -24), (key2797, 24), (key2810, -48), (key2833, 60), (key2899, -72), (key2915, 84), (key2940, 12), (key2945, -40), (key2952, 36), (key2962, -48), (key2978, 24), (key2985, -12), (key2999, 36), (key3004, -60)]

def entry10_2 : Integer.Sparse Key := [(key2370, -12), (key2376, 36), (key2388, -60), (key2398, 12), (key2404, -36), (key2435, 60), (key2478, 48), (key2501, -48), (key2583, 12), (key2589, 84), (key2604, -60), (key2762, -12), (key2768, -84), (key2916, 72), (key3005, 60), (key3019, -72)]

def entry10_5 : Integer.Sparse Key := [(key1526, 120), (key1534, -120), (key1604, -120), (key1640, 120), (key1679, 120), (key1693, -120)]

def entry10_6 : Integer.Sparse Key := [(key2414, 120), (key2419, -96), (key2426, 24), (key2487, -84), (key2494, 96), (key2572, 48), (key2573, -84), (key3038, -24), (key3043, -24), (key3120, -36), (key3130, 72), (key3141, 24), (key3144, -36)]

def entry10_7 : Integer.Sparse Key := [(key1259, 120), (key1271, -120), (key1534, -120), (key1679, 120), (key1894, 120), (key1916, -120)]

def entry10_8 : Integer.Sparse Key := [(key972, 120), (key978, -120), (key1086, -120), (key1163, 120), (key1227, 120), (key1244, -120)]

def entry10_9 : Integer.Sparse Key := [(key2374, 60), (key2380, -72), (key2408, -12), (key2439, 12), (key2468, -36), (key2481, 12), (key2505, 72), (key2535, -12), (key2537, 36), (key2542, -12), (key2553, -48), (key2591, 60), (key2596, -48), (key2775, 12), (key2847, -84), (key2878, 12), (key2884, 84), (key2917, -12), (key2926, 12), (key3006, -12), (key3020, 48), (key3029, -72)]

def entry11_0 : Integer.Sparse Key := [(key2770, 120), (key2773, -120), (key2847, -120), (key2881, 120), (key2890, 120), (key2911, -120)]

def entry11_1 : Integer.Sparse Key := [(key1249, 120), (key1262, -120), (key1524, -120), (key1645, 120), (key1762, 120), (key1803, -120)]

def entry11_2 : Integer.Sparse Key := [(key2588, 120), (key2599, -120), (key2767, -120), (key2888, 120), (key2930, 120), (key2967, -120)]

def entry11_3 : Integer.Sparse Key := [(key972, 120), (key977, -120), (key1086, -120), (key1162, 120), (key1181, 120), (key1218, -120)]

def entry11_4 : Integer.Sparse Key := [(key2369, 120), (key2384, -120), (key2397, -120), (key2431, 120), (key2474, 120), (key2497, -120)]

def entry11_5 : Integer.Sparse Key := [(key1527, 120), (key1532, -120), (key1605, -120), (key1638, 120), (key1649, 120), (key1672, -120)]

def entry11_6 : Integer.Sparse Key := [(key3034, 120), (key3037, -120), (key3121, -120), (key3129, 120), (key3133, 120), (key3139, -120)]

def entry11_7 : Integer.Sparse Key := [(key1257, 120), (key1266, -120), (key1532, -120), (key1649, 120), (key1766, 120), (key1807, -120)]

def entry11_8 : Integer.Sparse Key := [(key971, 120), (key975, -120), (key1085, -120), (key1161, 120), (key1179, 120), (key1217, -120)]

def entry11_9 : Integer.Sparse Key := [(key2591, 120), (key2594, -120), (key2847, -120), (key2881, 120), (key2969, 120), (key2990, -120)]

def entry11_10 : Integer.Sparse Key := [(key2354, 120), (key2358, -120), (key2449, -120), (key2514, 120), (key2529, 120), (key2559, -120)]

def entry11_11 : Integer.Sparse Key := [(key2353, 120), (key2356, -120), (key2448, -120), (key2513, 192), (key2527, 48), (key2558, -120)]

def entry12_0 : Integer.Sparse Key := [(key2616, 12), (key2619, -12), (key2632, -12), (key2642, 12), (key2649, 12), (key2654, -12), (key2671, -12), (key2674, 12), (key2706, 12), (key2729, -12), (key2738, -12), (key2748, 12), (key2786, 72), (key2794, -60), (key2796, -12), (key2809, -72), (key2829, 60), (key2832, 12), (key2860, 60), (key2870, -60), (key2898, 12), (key2905, -12), (key2939, 48), (key2944, -48), (key2951, -48), (key2961, 48), (key2977, 48), (key2984, -48)]

def entry12_1 : Integer.Sparse Key := [(key1288, 120), (key1308, -120), (key1383, -120), (key1416, 120), (key1538, 120), (key1565, -120)]

def entry12_2 : Integer.Sparse Key := [(key2609, 48), (key2613, 72), (key2625, -48), (key2629, -60), (key2637, -12), (key2647, -12), (key2652, 12), (key2664, -48), (key2668, -72), (key2699, 48), (key2703, 60), (key2723, 12), (key2736, 12), (key2746, -12), (key2779, 48), (key2783, 60), (key2791, 12), (key2802, -48), (key2806, -60), (key2826, -12), (key2896, -12), (key2903, 12), (key2937, 12), (key2942, -12), (key2949, -12), (key2959, 12), (key2975, 12), (key2982, -12)]

def entry12_3 : Integer.Sparse Key := [(key999, 120), (key1013, -120), (key1034, -120), (key1069, 120), (key1121, 120), (key1148, -120)]

def entry12_4 : Integer.Sparse Key := [(key2607, 120), (key2623, -120), (key2662, -120), (key2697, 120), (key2777, 120), (key2800, -120)]

def entry12_5 : Integer.Sparse Key := [(key1292, 12), (key1297, -12), (key1312, -12), (key1325, 12), (key1338, 12), (key1344, -12), (key1387, -12), (key1392, 12), (key1420, 12), (key1443, -12), (key1456, -12), (key1465, 12), (key1542, 12), (key1547, 60), (key1555, -72), (key1569, -12), (key1574, -60), (key1592, 72), (key1623, 60), (key1632, -60), (key1658, 12), (key1666, -12), (key1773, 48), (key1779, -48), (key1789, -48), (key1797, 48), (key1816, 48), (key1824, -48)]

def entry12_6 : Integer.Sparse Key := [(key3071, 120), (key3073, -120), (key3108, -120), (key3111, 120), (key3135, 120), (key3137, -120)]

def entry12_7 : Integer.Sparse Key := [(key1292, 48), (key1297, 72), (key1312, -48), (key1317, -60), (key1325, -12), (key1338, -12), (key1344, 12), (key1387, -48), (key1392, -72), (key1420, 48), (key1425, 60), (key1443, 12), (key1456, 12), (key1465, -12), (key1542, 48), (key1547, 60), (key1555, 12), (key1569, -48), (key1574, -60), (key1592, -12), (key1658, -12), (key1666, 12), (key1773, 12), (key1779, -12), (key1789, -12), (key1797, 12), (key1816, 12), (key1824, -12)]

def entry12_8 : Integer.Sparse Key := [(key997, 120), (key1012, -120), (key1032, -120), (key1068, 120), (key1120, 120), (key1147, -120)]

def entry12_9 : Integer.Sparse Key := [(key2616, -12), (key2619, 12), (key2632, 72), (key2640, -60), (key2642, -12), (key2649, 48), (key2654, -48), (key2671, 12), (key2674, -12), (key2706, -72), (key2726, 60), (key2729, 12), (key2738, -48), (key2748, 48), (key2786, -12), (key2796, 12), (key2809, 12), (key2832, -12), (key2860, 60), (key2870, -60), (key2898, 48), (key2905, -48), (key2939, 12), (key2944, -12), (key2951, -12), (key2961, 12), (key2977, 12), (key2984, -12)]

def entry12_10 : Integer.Sparse Key := [(key2375, 120), (key2387, -120), (key2403, -120), (key2434, 120), (key2477, 120), (key2500, -120)]

def entry12_11 : Integer.Sparse Key := [(key2370, -12), (key2373, 36), (key2386, -60), (key2398, 12), (key2401, -36), (key2433, 60), (key2476, 48), (key2499, -48), (key2583, 12), (key2586, 84), (key2597, -60), (key2762, -12), (key2765, -84), (key2886, 72), (key2928, 60), (key2965, -72)]

def entry12_12 : Integer.Sparse Key := [(key2608, 48), (key2611, 72), (key2624, -48), (key2627, -60), (key2636, -32), (key2645, 8), (key2651, 12), (key2663, -48), (key2666, -72), (key2698, 60), (key2701, 84), (key2722, 24), (key2745, -24), (key2778, 36), (key2781, 36), (key2790, 24), (key2801, -48), (key2804, -60), (key2825, -32), (key2895, -12), (key2902, 12), (key2947, 8), (key2958, 12), (key2974, 12), (key2981, -12)]

def entry13_0 : Integer.Sparse Key := [(key2175, 120), (key2179, -120), (key2275, -120), (key2281, 120), (key2328, 120), (key2330, -120)]

def entry13_1 : Integer.Sparse Key := [(key754, 120), (key755, -120), (key843, -120), (key844, 120), (key944, 120), (key945, -120)]

def entry13_2 : Integer.Sparse Key := [(key2079, 120), (key2085, -120), (key2176, -120), (key2187, 120), (key2279, 120), (key2287, -120)]

def entry13_3 : Integer.Sparse Key := [(key713, 120), (key715, -120), (key890, -120), (key914, 120), (key959, 120), (key966, -120)]

def entry13_4 : Integer.Sparse Key := [(key2098, 120), (key2099, -120), (key2203, -120), (key2206, 120), (key2318, 120), (key2321, -120)]

def entry13_5 : Integer.Sparse Key := [(key817, 120), (key818, -120), (key897, -120), (key902, 120), (key960, 120), (key962, -120)]

def entry13_6 : Integer.Sparse Key := [(key2182, 120), (key2183, -120), (key2284, -120), (key2285, 120), (key2345, 120), (key2346, -120)]

def entry13_7 : Integer.Sparse Key := [(key738, 120), (key743, -120), (key818, -120), (key825, 120), (key902, 120), (key908, -120)]

def entry13_8 : Integer.Sparse Key := [(key721, 120), (key722, -120), (key921, -120), (key939, 120), (key959, 120), (key966, -120)]

def entry13_9 : Integer.Sparse Key := [(key2078, 120), (key2082, -120), (key2275, -120), (key2289, 120), (key2328, 120), (key2333, -120)]

def entry13_10 : Integer.Sparse Key := [(key1998, 120), (key2000, -120), (key2267, -120), (key2292, 120), (key2340, 120), (key2349, -120)]

def entry13_11 : Integer.Sparse Key := [(key2006, 120), (key2007, -120), (key2299, -120), (key2313, 120), (key2340, 120), (key2349, -120)]

def entry13_12 : Integer.Sparse Key := [(key2092, 120), (key2095, -120), (key2194, -120), (key2200, 120), (key2305, 120), (key2310, -120)]

def entry13_13 : Integer.Sparse Key := [(key776, 120), (key778, -120), (key801, -120), (key811, 192), (key836, 48), (key839, -120)]

def entry14_0 : Integer.Sparse Key := [(key2379, 6), (key2382, -6), (key2393, 14), (key2407, 54), (key2410, -30), (key2441, 56), (key2445, -42), (key2473, -36), (key2483, 30), (key2507, -24), (key2526, 42), (key2539, 24), (key2544, -32), (key2555, -8), (key2557, 18), (key2565, -30), (key2592, -6), (key2595, 6), (key2602, -14), (key2771, 6), (key2774, -30), (key2848, -24), (key2882, 36), (key2891, 30), (key2912, -28), (key2933, 4), (key2934, -18), (key2970, -36), (key2991, 8), (key2993, 42), (key2996, 18), (key3003, -30)]

def entry14_1 : Integer.Sparse Key := [(key1254, 120), (key1263, -120), (key1529, -120), (key1646, 120), (key1763, 120), (key1804, -120)]

def entry14_2 : Integer.Sparse Key := [(key2378, 12), (key2383, 24), (key2390, -36), (key2394, -36), (key2406, -12), (key2411, -24), (key2437, 36), (key2443, 36), (key2480, 24), (key2484, 24), (key2503, -24), (key2509, -24), (key2587, 48), (key2593, 36), (key2598, -24), (key2600, -24), (key2766, -48), (key2772, -36), (key2887, 36), (key2889, 36), (key2929, 24), (key2931, 24), (key2966, -36), (key2968, -36)]

def entry14_3 : Integer.Sparse Key := [(key976, 120), (key984, -120), (key1090, -120), (key1169, 120), (key1183, 120), (key1220, -120)]

def entry14_4 : Integer.Sparse Key := [(key2377, 120), (key2389, -120), (key2405, -120), (key2436, 120), (key2479, 120), (key2502, -120)]

def entry14_5 : Integer.Sparse Key := [(key1531, 60), (key1536, -60), (key1609, -60), (key1642, 60), (key1651, 60), (key1674, -60), (key1765, 60), (key1768, -60), (key1806, -60), (key1832, 60), (key1837, 60), (key1848, -60)]

def entry14_6 : Integer.Sparse Key := [(key2428, 156), (key2430, -96), (key2444, 12), (key2496, -96), (key2510, 96), (key2574, 48), (key2577, -84), (key3040, -36), (key3042, -24), (key3044, -12), (key3132, -24), (key3140, 72), (key3145, 24), (key3148, -36)]

def entry14_7 : Integer.Sparse Key := [(key1256, 60), (key1261, 60), (key1265, -60), (key1268, -60), (key1531, -60), (key1536, -60), (key1648, 60), (key1651, 60), (key1765, 60), (key1768, 60), (key1806, -60), (key1809, -60)]

def entry14_8 : Integer.Sparse Key := [(key976, 120), (key983, -120), (key1090, -120), (key1168, 120), (key1182, 120), (key1219, -120)]

def entry14_9 : Integer.Sparse Key := [(key2379, 54), (key2382, -30), (key2393, 56), (key2395, -42), (key2407, 6), (key2410, -6), (key2441, 14), (key2473, -36), (key2483, -24), (key2507, 30), (key2526, 42), (key2539, 24), (key2544, -8), (key2545, 18), (key2555, -32), (key2565, -30), (key2592, 6), (key2595, -30), (key2602, 4), (key2603, -18), (key2771, -6), (key2774, 6), (key2848, -24), (key2882, 36), (key2891, -36), (key2912, 8), (key2914, 42), (key2933, -14), (key2970, 30), (key2991, -28), (key2996, 18), (key3003, -30)]

def entry14_10 : Integer.Sparse Key := [(key2361, 120), (key2363, -44), (key2366, -76), (key2452, -36), (key2456, -84), (key2517, 12), (key2519, 84), (key2523, 96), (key2528, -12), (key2530, 24), (key2560, -48), (key2567, 36), (key2579, -72)]

def entry14_11 : Integer.Sparse Key := [(key2361, 120), (key2364, -120), (key2456, -120), (key2520, 120), (key2531, 120), (key2561, -120)]

def entry14_12 : Integer.Sparse Key := [(key2378, 60), (key2381, 60), (key2390, -60), (key2392, -60), (key2406, -60), (key2409, -60), (key2437, 60), (key2440, 60), (key2480, 60), (key2482, 60), (key2503, -60), (key2506, -60)]

def entry14_13 : Integer.Sparse Key := [(key1999, 120), (key2003, -120), (key2268, -120), (key2294, 120), (key2324, 120), (key2336, -120)]

def entry14_14 : Integer.Sparse Key := [(key2362, 60), (key2367, -60), (key2457, -60), (key2460, -60), (key2521, 88), (key2525, 84), (key2532, 32), (key2533, 36), (key2562, -60), (key2564, -60)]

def entry15_0 : Integer.Sparse Key := [(key2616, 48), (key2618, -18), (key2621, -30), (key2628, -12), (key2632, -36), (key2640, 6), (key2641, 30), (key2644, 36), (key2646, -6), (key2648, 12), (key2653, -18), (key2658, 18), (key2660, -30), (key2671, 12), (key2673, -6), (key2676, -6), (key2706, -12), (key2728, 12), (key2732, 18), (key2735, -12), (key2737, 6), (key2747, -12), (key2753, 6), (key2758, -18), (key2786, -12), (key2794, 12), (key2795, 6), (key2798, 6), (key2805, -12), (key2809, 24), (key2829, 52), (key2831, -12), (key2835, -54), (key2860, -6), (key2870, -36), (key2885, 42), (key2893, 6), (key2897, -6), (key2904, 6), (key2920, -6), (key2923, 30), (key2927, -36), (key2938, -6), (key2943, 6), (key2948, 8), (key2950, -18), (key2960, 4), (key2972, -24), (key2976, 42), (key2997, 18), (key2998, -24), (key3000, -6), (key3017, 8), (key3023, 6), (key3026, -12), (key3030, 6)]

def entry15_1 : Integer.Sparse Key := [(key1417, 120), (key1471, -120), (key1566, -120), (key1680, 120), (key1902, 120), (key1917, -120)]

def entry15_2 : Integer.Sparse Key := [(key2608, 12), (key2614, -12), (key2624, -12), (key2638, 24), (key2659, -12), (key2663, -12), (key2669, 12), (key2698, 18), (key2704, 66), (key2724, 36), (key2752, -72), (key2757, -48), (key2778, 6), (key2784, -6), (key2792, -12), (key2801, -12), (key2807, -60), (key2827, -44), (key2858, 18), (key2868, -18), (key2918, 42), (key2919, 12), (key2922, 30), (key3009, 12), (key3011, 68), (key3016, 48), (key3021, -42), (key3022, 6), (key3025, -48)]

def entry15_3 : Integer.Sparse Key := [(key1028, 120), (key1036, -120), (key1106, -120), (key1123, 120), (key1232, 120), (key1235, -120)]

def entry15_4 : Integer.Sparse Key := [(key2780, 120), (key2789, -120), (key2803, -120), (key2824, 120), (key2855, 120), (key2865, -120)]

def entry15_5 : Integer.Sparse Key := [(key1291, 48), (key1299, -48), (key1311, -48), (key1327, 48), (key1352, 48), (key1355, -48), (key1386, 12), (key1394, -12), (key1419, -12), (key1445, 12), (key1473, 12), (key1481, -12), (key1541, -12), (key1557, 12), (key1568, 72), (key1576, -60), (key1594, -12), (key1617, -60), (key1625, 60), (key1682, 60), (key1684, -72), (key1690, 12), (key1897, 12), (key1900, -12), (key1904, -12), (key1912, 12), (key1921, 12), (key1927, -12)]

def entry15_6 : Integer.Sparse Key := [(key2679, 72), (key2684, -60), (key2691, 4), (key2710, -84), (key2717, 96), (key2754, 48), (key2755, -84), (key2813, 8), (key2820, -12), (key3014, 8), (key3047, 48), (key3053, -60), (key3058, -4), (key3061, -36), (key3068, 72), (key3075, 24), (key3076, -36), (key3096, -8), (key3113, 12), (key3115, -8)]

def entry15_7 : Integer.Sparse Key := [(key1291, 12), (key1299, -12), (key1311, -12), (key1327, 12), (key1352, 12), (key1355, -12), (key1386, -12), (key1394, 12), (key1419, 12), (key1427, 60), (key1445, 48), (key1473, -72), (key1481, -48), (key1541, 12), (key1557, -12), (key1568, -12), (key1576, -60), (key1594, -48), (key1682, 60), (key1684, 12), (key1690, 48), (key1897, -12), (key1900, 12), (key1904, 72), (key1912, 48), (key1919, -60), (key1921, -12), (key1927, -48)]

def entry15_8 : Integer.Sparse Key := [(key1029, 120), (key1035, -120), (key1107, -120), (key1122, 120), (key1231, 120), (key1234, -120)]

def entry15_9 : Integer.Sparse Key := [(key2616, 12), (key2618, -6), (key2621, -6), (key2632, -12), (key2640, 12), (key2641, 12), (key2644, 6), (key2646, -12), (key2648, 6), (key2653, -12), (key2667, -6), (key2671, 54), (key2673, -12), (key2676, -36), (key2702, -12), (key2706, 18), (key2726, 60), (key2728, 30), (key2732, -60), (key2735, -6), (key2737, 12), (key2747, -18), (key2753, -6), (key2758, 18), (key2782, -6), (key2786, -36), (key2794, 6), (key2795, -6), (key2798, 36), (key2809, -12), (key2831, 6), (key2835, 18), (key2860, -6), (key2870, -36), (key2885, 42), (key2893, 6), (key2897, 6), (key2904, -6), (key2920, 6), (key2923, -12), (key2927, 6), (key2938, -12), (key2943, -6), (key2950, -6), (key2960, 6), (key2972, -24), (key2983, 42), (key2997, 18), (key2998, -6), (key3000, -24), (key3008, 18), (key3010, -30), (key3012, 6), (key3017, -18), (key3023, -6), (key3026, 30), (key3030, -36)]

def entry15_10 : Integer.Sparse Key := [(key2370, 12), (key2376, -12), (key2388, 12), (key2398, 108), (key2404, -72), (key2464, -76), (key2478, 84), (key2501, 12), (key2568, 36), (key2570, -60), (key2575, -12), (key2583, -12), (key2589, 12), (key2604, -12), (key2762, 12), (key2768, -48), (key2839, -44), (key2876, 84), (key2916, 36), (key2925, -60), (key3019, -12), (key3028, 12)]

def entry15_11 : Integer.Sparse Key := [(key2763, 120), (key2767, -120), (key2840, -120), (key2875, 120), (key2888, 120), (key2909, -120)]

def entry15_12 : Integer.Sparse Key := [(key2609, 12), (key2613, -12), (key2625, -12), (key2637, 12), (key2647, 12), (key2652, -12), (key2664, -12), (key2668, 12), (key2699, 12), (key2723, -12), (key2736, -12), (key2746, 12), (key2779, 12), (key2783, 60), (key2791, -72), (key2802, -12), (key2806, -60), (key2826, 72), (key2857, 60), (key2867, -60), (key2896, 12), (key2903, -12), (key2937, 48), (key2942, -48), (key2949, -48), (key2959, 48), (key2975, 48), (key2982, -48)]

def entry15_13 : Integer.Sparse Key := [(key2174, 120), (key2176, -120), (key2274, -120), (key2279, 120), (key2341, 120), (key2343, -120)]

def entry15_14 : Integer.Sparse Key := [(key2383, -6), (key2390, 12), (key2394, 6), (key2406, 72), (key2411, -42), (key2437, 60), (key2443, -42), (key2472, -48), (key2484, 42), (key2503, -36), (key2509, 6), (key2524, 48), (key2569, 24), (key2571, -36), (key2576, 12), (key2580, -36), (key2593, 6), (key2598, -12), (key2600, -6), (key2766, -12), (key2772, -18), (key2843, -12), (key2880, 36), (key2889, 18), (key2910, -24), (key2931, -18), (key2966, -24), (key2968, -6), (key2989, 48), (key2995, 12), (key3002, -24)]

def entry15_15 : Integer.Sparse Key := [(key2608, 48), (key2614, -48), (key2624, -48), (key2638, 72), (key2657, 24), (key2659, -48), (key2663, 12), (key2669, -12), (key2698, -32), (key2704, 12), (key2724, 24), (key2757, -24), (key2778, 8), (key2784, -12), (key2792, 24), (key2801, 72), (key2807, -60), (key2827, -32), (key2851, -60), (key2858, 72), (key2868, 12), (key2918, 48), (key2919, -72), (key3011, 8), (key3016, 12), (key3021, -12), (key3022, 24), (key3025, -12)]

def entry16_0 : Integer.Sparse Key := [(key2616, -24), (key2619, 24), (key2632, 24), (key2642, -24), (key2649, -24), (key2654, 24), (key2671, 24), (key2674, -24), (key2706, -24), (key2729, 24), (key2738, 24), (key2748, -24), (key2786, 96), (key2796, -96), (key2809, -96), (key2832, 96), (key2898, 96), (key2905, -96), (key2939, 24), (key2944, -24), (key2951, -24), (key2961, 24), (key2977, 24), (key2984, -24)]

def entry16_1 : Integer.Sparse Key := [(key1288, 120), (key1334, -120), (key1383, -120), (key1452, 120), (key1769, 120), (key1785, -120)]

def entry16_2 : Integer.Sparse Key := [(key2609, 24), (key2613, 96), (key2625, -24), (key2637, 24), (key2647, -96), (key2652, -24), (key2664, -24), (key2668, -96), (key2699, 24), (key2723, -24), (key2736, 96), (key2746, 24), (key2779, 24), (key2791, -24), (key2802, -24), (key2826, 24), (key2896, 24), (key2903, -24), (key2937, 96), (key2942, 24), (key2949, -96), (key2959, -24), (key2975, -24), (key2982, 24)]

def entry16_3 : Integer.Sparse Key := [(key994, 120), (key1013, -120), (key1029, -120), (key1069, 120), (key1197, 120), (key1210, -120)]

def entry16_4 : Integer.Sparse Key := [(key2607, 120), (key2634, -120), (key2662, -120), (key2720, 120), (key2788, 120), (key2823, -120)]

def entry16_5 : Integer.Sparse Key := [(key1292, -24), (key1297, 24), (key1312, 24), (key1325, -24), (key1338, -24), (key1344, 24), (key1387, 24), (key1392, -24), (key1420, -24), (key1443, 24), (key1456, 24), (key1465, -24), (key1542, 96), (key1555, -96), (key1569, -96), (key1592, 96), (key1658, 96), (key1666, -96), (key1773, 24), (key1779, -24), (key1789, -24), (key1797, 24), (key1816, 24), (key1824, -24)]

def entry16_6 : Integer.Sparse Key := [(key3062, 120), (key3067, -120), (key3097, -120), (key3104, 120), (key3135, 120), (key3137, -120)]

def entry16_7 : Integer.Sparse Key := [(key1292, 24), (key1297, 96), (key1312, -24), (key1325, 24), (key1338, -96), (key1344, -24), (key1387, -24), (key1392, -96), (key1420, 24), (key1443, -24), (key1456, 96), (key1465, 24), (key1542, 24), (key1555, -24), (key1569, -24), (key1592, 24), (key1658, 24), (key1666, -24), (key1773, 96), (key1779, 24), (key1789, -96), (key1797, -24), (key1816, -24), (key1824, 24)]

def entry16_8 : Integer.Sparse Key := [(key993, 120), (key1012, -120), (key1028, -120), (key1068, 120), (key1196, 120), (key1209, -120)]

def entry16_9 : Integer.Sparse Key := [(key2616, 24), (key2619, -24), (key2632, 96), (key2642, -96), (key2649, 24), (key2654, -24), (key2671, -24), (key2674, 24), (key2706, -96), (key2729, 96), (key2738, -24), (key2748, 24), (key2786, 24), (key2796, -24), (key2809, -24), (key2832, 24), (key2898, 24), (key2905, -24), (key2939, -24), (key2944, 24), (key2951, 24), (key2961, -24), (key2977, 96), (key2984, -96)]

def entry16_10 : Integer.Sparse Key := [(key2371, 120), (key2387, -120), (key2399, -120), (key2434, 120), (key2541, 120), (key2552, -120)]

def entry16_11 : Integer.Sparse Key := [(key2370, 84), (key2373, -24), (key2386, -72), (key2398, -84), (key2401, 24), (key2433, 72), (key2476, -24), (key2499, 24), (key2540, 48), (key2551, -48), (key2583, 36), (key2586, 24), (key2597, -48), (key2762, -36), (key2765, -24), (key2886, 24), (key2908, 72), (key2928, 48), (key2965, -24), (key2987, -72)]

def entry16_12 : Integer.Sparse Key := [(key2608, 24), (key2611, 96), (key2624, -24), (key2636, -12), (key2645, -60), (key2651, -24), (key2663, -24), (key2666, -96), (key2698, 36), (key2722, 36), (key2734, 60), (key2745, 36), (key2778, 12), (key2790, 12), (key2801, -24), (key2825, -12), (key2895, 24), (key2902, -24), (key2935, 36), (key2941, 12), (key2947, -60), (key2958, -24), (key2974, -24), (key2981, 24)]

def entry16_13 : Integer.Sparse Key := [(key2091, 120), (key2095, -120), (key2193, -120), (key2200, 120), (key2343, 120), (key2347, -120)]

def entry16_14 : Integer.Sparse Key := [(key2378, 120), (key2392, -120), (key2406, -120), (key2440, 120), (key2543, 120), (key2554, -120)]

def entry16_15 : Integer.Sparse Key := [(key2609, -24), (key2613, 24), (key2625, 24), (key2637, -24), (key2647, -24), (key2652, 24), (key2664, 24), (key2668, -24), (key2699, -24), (key2723, 24), (key2736, 24), (key2746, -24), (key2779, 96), (key2791, -96), (key2802, -96), (key2826, 96), (key2896, 96), (key2903, -96), (key2937, 24), (key2942, -24), (key2949, -24), (key2959, 24), (key2975, 24), (key2982, -24)]

def entry16_16 : Integer.Sparse Key := [(key2608, 72), (key2611, 48), (key2624, 48), (key2645, -96), (key2651, -72), (key2663, -72), (key2666, -48), (key2698, -96), (key2722, 48), (key2734, 96), (key2745, 96), (key2801, 48), (key2895, -48), (key2902, 48), (key2935, 48), (key2941, 48), (key2947, -96), (key2958, -72), (key2974, 48), (key2981, -48)]

def entry17_0 : Integer.Sparse Key := [(key1296, 48), (key1302, -48), (key1316, -48), (key1329, 48), (key1339, 48), (key1345, -48), (key1391, 12), (key1397, -12), (key1424, -12), (key1447, 12), (key1457, 12), (key1466, -12), (key1546, -12), (key1559, 12), (key1573, 12), (key1596, -12), (key1659, -12), (key1667, 12), (key1774, 12), (key1780, -12), (key1788, 60), (key1790, -72), (key1798, 12), (key1813, -60), (key1817, 72), (key1825, -12), (key1839, 60), (key1841, -60)]

def entry17_1 : Integer.Sparse Key := [(key384, 120), (key393, -120), (key405, -120), (key416, 120), (key438, 120), (key448, -120)]

def entry17_2 : Integer.Sparse Key := [(key1292, 12), (key1298, -12), (key1312, -12), (key1326, 12), (key1351, 12), (key1354, -12), (key1387, -12), (key1393, 12), (key1420, 12), (key1444, -12), (key1472, -12), (key1480, 12), (key1542, 12), (key1548, 60), (key1556, -72), (key1569, -12), (key1575, -60), (key1593, 72), (key1624, 60), (key1633, -60), (key1683, 12), (key1689, -12), (key1896, 48), (key1899, -48), (key1903, -48), (key1911, 48), (key1920, 48), (key1926, -48)]

def entry17_3 : Integer.Sparse Key := [(key44, 120), (key47, -120), (key101, -120), (key114, 120), (key172, 120), (key176, -120)]

def entry17_4 : Integer.Sparse Key := [(key1540, 120), (key1552, -120), (key1567, -120), (key1589, 120), (key1620, 120), (key1629, -120)]

def entry17_5 : Integer.Sparse Key := [(key237, 48), (key240, -48), (key249, -48), (key262, 48), (key268, 48), (key273, -48), (key303, 12), (key306, -12), (key317, -12), (key330, 12), (key336, 12), (key342, -12), (key386, -12), (key399, 12), (key407, 72), (key410, -60), (key420, -12), (key436, -60), (key444, 60), (key468, 60), (key471, -72), (key477, 12), (key569, 12), (key574, -12), (key579, -12), (key585, 12), (key597, 12), (key603, -12)]

def entry17_6 : Integer.Sparse Key := [(key1406, 120), (key1409, -120), (key1434, -120), (key1438, 120), (key1476, 120), (key1478, -120)]

def entry17_7 : Integer.Sparse Key := [(key237, 12), (key240, -12), (key249, -12), (key262, 12), (key268, 12), (key273, -12), (key303, -12), (key306, 12), (key317, 12), (key320, 60), (key330, 48), (key336, -72), (key342, -48), (key386, 12), (key399, -12), (key407, -12), (key410, -60), (key420, -48), (key468, 60), (key471, 12), (key477, 48), (key569, -12), (key574, 12), (key579, 72), (key585, 48), (key594, -60), (key597, -12), (key603, -48)]

def entry17_8 : Integer.Sparse Key := [(key18, 12), (key21, -12), (key32, 12), (key43, 108), (key46, -72), (key100, -76), (key112, 84), (key134, 12), (key171, 36), (key174, -60), (key179, -12), (key206, -12), (key209, 12), (key214, -12), (key375, 12), (key378, -48), (key426, -44), (key457, 84), (key463, 36), (key480, -60), (key589, -12), (key606, 12)]

def entry17_9 : Integer.Sparse Key := [(key1296, 12), (key1302, -12), (key1316, -12), (key1329, 12), (key1339, 12), (key1345, -12), (key1391, 48), (key1397, -48), (key1424, -48), (key1447, 48), (key1457, 48), (key1466, -48), (key1546, 12), (key1559, -12), (key1573, -12), (key1596, 12), (key1659, 12), (key1667, -12), (key1772, 60), (key1774, -72), (key1780, 12), (key1790, 12), (key1798, -12), (key1813, -60), (key1817, -12), (key1825, 72), (key1839, 60), (key1844, -60)]

def entry17_10 : Integer.Sparse Key := [(key1527, 120), (key1533, -120), (key1605, -120), (key1639, 120), (key1678, 120), (key1692, -120)]

def entry17_11 : Integer.Sparse Key := [(key1526, 120), (key1530, -120), (key1604, -120), (key1637, 120), (key1647, 120), (key1671, -120)]

def entry17_12 : Integer.Sparse Key := [(key1291, 12), (key1295, -12), (key1311, -12), (key1324, 12), (key1336, 12), (key1343, -12), (key1386, -12), (key1390, 12), (key1419, 12), (key1442, -12), (key1454, -12), (key1464, 12), (key1541, 12), (key1545, 60), (key1554, -72), (key1568, -12), (key1572, -60), (key1591, 72), (key1622, 60), (key1631, -60), (key1657, 12), (key1665, -12), (key1771, 48), (key1778, -48), (key1787, -48), (key1796, 48), (key1815, 48), (key1823, -48)]

def entry17_13 : Integer.Sparse Key := [(key830, 120), (key831, -120), (key924, -120), (key928, 120), (key960, 120), (key962, -120)]

def entry17_14 : Integer.Sparse Key := [(key1531, 60), (key1535, -60), (key1609, -60), (key1641, 60), (key1650, 60), (key1673, -60), (key1765, 60), (key1767, -60), (key1806, -60), (key1831, 60), (key1836, 60), (key1847, -60)]

def entry17_15 : Integer.Sparse Key := [(key1292, 48), (key1298, -48), (key1312, -48), (key1326, 48), (key1351, 48), (key1354, -48), (key1387, 12), (key1393, -12), (key1420, -12), (key1444, 12), (key1472, 12), (key1480, -12), (key1542, -12), (key1556, 12), (key1569, 72), (key1575, -60), (key1593, -12), (key1618, -60), (key1624, 60), (key1681, 60), (key1683, -72), (key1689, 12), (key1896, 12), (key1899, -12), (key1903, -12), (key1911, 12), (key1920, 12), (key1926, -12)]

def entry17_16 : Integer.Sparse Key := [(key1291, -24), (key1295, 24), (key1311, 24), (key1324, -24), (key1336, -24), (key1343, 24), (key1386, 24), (key1390, -24), (key1419, -24), (key1442, 24), (key1454, 24), (key1464, -24), (key1541, 96), (key1554, -96), (key1568, -96), (key1591, 96), (key1657, 96), (key1665, -96), (key1771, 24), (key1778, -24), (key1787, -24), (key1796, 24), (key1815, 24), (key1823, -24)]

def entry17_17 : Integer.Sparse Key := [(key236, 48), (key239, -48), (key248, -48), (key260, 72), (key267, 24), (key271, -48), (key302, 12), (key305, -12), (key316, -32), (key319, 12), (key328, 24), (key340, -24), (key385, 8), (key388, -12), (key397, 24), (key406, 72), (key409, -60), (key418, -32), (key435, -60), (key442, 72), (key450, 12), (key467, 48), (key469, -72), (key578, 8), (key583, 12), (key593, -12), (key595, 24), (key601, -12)]

def entry18_0 : Integer.Sparse Key := [(key2616, 48), (key2619, -48), (key2632, -48), (key2642, 48), (key2649, 48), (key2654, -48), (key2671, 12), (key2674, -12), (key2706, -12), (key2729, 12), (key2738, 12), (key2748, -12), (key2786, -12), (key2796, 12), (key2809, 12), (key2829, 60), (key2832, -72), (key2870, -60), (key2883, 60), (key2898, -12), (key2905, 72), (key2913, -60), (key2939, 12), (key2944, -12), (key2951, -12), (key2961, 12), (key2977, 12), (key2984, -12)]

def entry18_1 : Integer.Sparse Key := [(key1416, 120), (key1452, -120), (key1565, -120), (key1652, 120), (key1785, 120), (key1810, -120)]

def entry18_2 : Integer.Sparse Key := [(key2609, 12), (key2613, -12), (key2625, -12), (key2637, 12), (key2647, 12), (key2652, -12), (key2664, -12), (key2668, 12), (key2699, 12), (key2703, 60), (key2723, 48), (key2736, -72), (key2746, -48), (key2779, 12), (key2791, -12), (key2802, -12), (key2806, -60), (key2826, -48), (key2894, 60), (key2896, 12), (key2903, 48), (key2937, -12), (key2942, 12), (key2949, 72), (key2959, 48), (key2973, -60), (key2975, -12), (key2982, -48)]

def entry18_3 : Integer.Sparse Key := [(key1029, 120), (key1034, -120), (key1107, -120), (key1121, 120), (key1191, 120), (key1197, -120)]

def entry18_4 : Integer.Sparse Key := [(key2777, 120), (key2788, -120), (key2800, -120), (key2823, 120), (key2854, 120), (key2864, -120)]

def entry18_5 : Integer.Sparse Key := [(key1292, 48), (key1297, -48), (key1312, -48), (key1325, 48), (key1338, 48), (key1344, -48), (key1387, 12), (key1392, -12), (key1420, -12), (key1443, 12), (key1456, 12), (key1465, -12), (key1542, -12), (key1555, 12), (key1569, 72), (key1574, -60), (key1592, -12), (key1618, -60), (key1623, 60), (key1656, 60), (key1658, -72), (key1666, 12), (key1773, 12), (key1779, -12), (key1789, -12), (key1797, 12), (key1816, 12), (key1824, -12)]

def entry18_6 : Integer.Sparse Key := [(key3048, 120), (key3052, -120), (key3062, -120), (key3067, 120), (key3071, 120), (key3073, -120)]

def entry18_7 : Integer.Sparse Key := [(key1292, 12), (key1297, -12), (key1312, -12), (key1325, 12), (key1338, 12), (key1344, -12), (key1387, -12), (key1392, 12), (key1420, 12), (key1425, 60), (key1443, 48), (key1456, -72), (key1465, -48), (key1542, 12), (key1555, -12), (key1569, -12), (key1574, -60), (key1592, -48), (key1656, 60), (key1658, 12), (key1666, 48), (key1773, -12), (key1779, 12), (key1789, 72), (key1797, 48), (key1814, -60), (key1816, -12), (key1824, -48)]

def entry18_8 : Integer.Sparse Key := [(key1028, 120), (key1032, -120), (key1106, -120), (key1120, 120), (key1189, 120), (key1196, -120)]

def entry18_9 : Integer.Sparse Key := [(key2616, 12), (key2619, -12), (key2632, -12), (key2642, 12), (key2649, 12), (key2654, -12), (key2671, 48), (key2674, -48), (key2706, 12), (key2726, 60), (key2729, -72), (key2738, -12), (key2748, 12), (key2786, -48), (key2796, 48), (key2809, -12), (key2832, 12), (key2870, -60), (key2883, 60), (key2898, 12), (key2905, -12), (key2939, 48), (key2944, -48), (key2951, 12), (key2961, -12), (key2977, -12), (key2984, 72), (key2992, -60)]

def entry18_10 : Integer.Sparse Key := [(key2399, 120), (key2403, -120), (key2465, -120), (key2477, 120), (key2536, 120), (key2541, -120)]

def entry18_11 : Integer.Sparse Key := [(key2370, 12), (key2373, -12), (key2386, 12), (key2398, 108), (key2401, -72), (key2464, -76), (key2476, 84), (key2499, 12), (key2534, 36), (key2540, -60), (key2551, -12), (key2583, -12), (key2586, 12), (key2597, -12), (key2762, 12), (key2765, -48), (key2839, -44), (key2874, 84), (key2886, 36), (key2908, -60), (key2965, -12), (key2987, 12)]

def entry18_12 : Integer.Sparse Key := [(key2608, 12), (key2611, -12), (key2624, -12), (key2636, 24), (key2651, -12), (key2663, -12), (key2666, 12), (key2698, 18), (key2701, 66), (key2722, 36), (key2734, -72), (key2745, -48), (key2778, 6), (key2781, -6), (key2790, -12), (key2801, -12), (key2804, -60), (key2825, -44), (key2856, 18), (key2866, -18), (key2892, 42), (key2895, 12), (key2902, 30), (key2941, 12), (key2947, 68), (key2958, 48), (key2971, -42), (key2974, 6), (key2981, -48)]

def entry18_13 : Integer.Sparse Key := [(key2193, 120), (key2194, -120), (key2302, -120), (key2305, 120), (key2341, 120), (key2343, -120)]

def entry18_14 : Integer.Sparse Key := [(key2406, 60), (key2409, -60), (key2437, 60), (key2440, -60), (key2472, -60), (key2482, 60), (key2503, -60), (key2522, 60), (key2538, 60), (key2543, -60), (key2554, 60), (key2563, -60)]

def entry18_15 : Integer.Sparse Key := [(key2609, 48), (key2613, -48), (key2625, -48), (key2637, 48), (key2647, 48), (key2652, -48), (key2664, 12), (key2668, -12), (key2699, -12), (key2723, 12), (key2736, 12), (key2746, -12), (key2779, -12), (key2791, 12), (key2802, 72), (key2806, -60), (key2826, -12), (key2852, -60), (key2857, 60), (key2894, 60), (key2896, -72), (key2903, 12), (key2937, 12), (key2942, -12), (key2949, -12), (key2959, 12), (key2975, 12), (key2982, -12)]

def entry18_16 : Integer.Sparse Key := [(key2608, -24), (key2611, 24), (key2624, 24), (key2636, -24), (key2645, -24), (key2651, 24), (key2663, 24), (key2666, -24), (key2698, 96), (key2701, 12), (key2722, 36), (key2734, -60), (key2745, -36), (key2778, -24), (key2781, -12), (key2790, -12), (key2801, -96), (key2825, 12), (key2856, -12), (key2866, 12), (key2892, 12), (key2895, 96), (key2902, -12), (key2935, 12), (key2941, -12), (key2947, 60), (key2958, 24), (key2971, -12), (key2974, -60), (key2981, -24)]

def entry18_17 : Integer.Sparse Key := [(key1291, 48), (key1295, -48), (key1311, -48), (key1324, 48), (key1336, 48), (key1343, -48), (key1386, 12), (key1390, -12), (key1419, -12), (key1442, 12), (key1454, 12), (key1464, -12), (key1541, -12), (key1554, 12), (key1568, 72), (key1572, -60), (key1591, -12), (key1617, -60), (key1622, 60), (key1654, 60), (key1657, -72), (key1665, 12), (key1771, 12), (key1778, -12), (key1787, -12), (key1796, 12), (key1815, 12), (key1823, -12)]

def entry18_18 : Integer.Sparse Key := [(key2608, 48), (key2611, -48), (key2624, -48), (key2636, 72), (key2645, 24), (key2651, -48), (key2663, 12), (key2666, -12), (key2698, -32), (key2701, 12), (key2722, 24), (key2745, -24), (key2778, 8), (key2781, -12), (key2790, 24), (key2801, 72), (key2804, -60), (key2825, -32), (key2851, -60), (key2856, 72), (key2866, 12), (key2892, 48), (key2895, -72), (key2947, 8), (key2958, 12), (key2971, -12), (key2974, 24), (key2981, -12)]

def entry19_0 : Integer.Sparse Key := [(key1492, 120), (key1496, -120), (key1718, -120), (key1728, 120), (key1865, 120), (key1870, -120)]

def entry19_1 : Integer.Sparse Key := [(key281, 120), (key290, -120), (key350, -120), (key367, 120), (key516, 120), (key538, -120)]

def entry19_2 : Integer.Sparse Key := [(key1367, 120), (key1376, -120), (key1493, -120), (key1515, 120), (key1725, 120), (key1743, -120)]

def entry19_3 : Integer.Sparse Key := [(key29, 60), (key33, -72), (key109, -48), (key149, 96), (key175, 24), (key185, -60), (key223, 60), (key228, -48), (key495, -72), (key554, 96), (key665, 24), (key682, -60)]

def entry19_4 : Integer.Sparse Key := [(key1361, 120), (key1373, -120), (key1487, -120), (key1512, 120), (key1722, 120), (key1740, -120)]

def entry19_5 : Integer.Sparse Key := [(key257, -12), (key261, 12), (key272, -12), (key282, 12), (key285, -12), (key295, 12), (key351, 120), (key354, -72), (key398, -48), (key439, -36), (key458, 84), (key470, 36), (key481, -60), (key508, -84), (key523, 84), (key543, 12), (key596, -12), (key607, 12), (key668, 36), (key672, -60), (key678, -12)]

def entry19_6 : Integer.Sparse Key := [(key1502, 120), (key1504, -120), (key1734, -120), (key1737, 120), (key1945, 120), (key1947, -120)]

def entry19_7 : Integer.Sparse Key := [(key257, 12), (key261, 128), (key272, -108), (key282, -12), (key285, -8), (key295, -12), (key351, 12), (key354, -36), (key371, 60), (key394, -12), (key398, -84), (key470, 72), (key523, 48), (key543, -48), (key573, 60), (key596, -72)]

def entry19_8 : Integer.Sparse Key := [(key223, 120), (key226, -120), (key495, -120), (key552, 120), (key620, 120), (key646, -120)]

def entry19_9 : Integer.Sparse Key := [(key1366, 120), (key1370, -120), (key1718, -120), (key1747, 120), (key1865, 120), (key1880, -120)]

def entry19_10 : Integer.Sparse Key := [(key1276, 120), (key1281, -120), (key1699, -120), (key1753, 120), (key1934, 120), (key1954, -120)]

def entry19_11 : Integer.Sparse Key := [(key1276, 120), (key1279, -120), (key1699, -120), (key1752, 120), (key1853, 120), (key1885, -120)]

def entry19_12 : Integer.Sparse Key := [(key1365, 120), (key1375, -120), (key1491, -120), (key1514, 120), (key1724, 120), (key1742, -120)]

def entry19_13 : Integer.Sparse Key := [(key741, 120), (key742, -120), (key900, -120), (key913, 120), (key951, 120), (key954, -120)]

def entry19_14 : Integer.Sparse Key := [(key1280, 120), (key1284, -120), (key1703, -120), (key1757, 120), (key1856, 120), (key1887, -120)]

def entry19_15 : Integer.Sparse Key := [(key1488, 120), (key1493, -120), (key1714, -120), (key1725, 120), (key1938, 120), (key1941, -120)]

def entry19_16 : Integer.Sparse Key := [(key1362, 120), (key1375, -120), (key1488, -120), (key1514, 120), (key1868, 120), (key1878, -120)]

def entry19_17 : Integer.Sparse Key := [(key351, 120), (key353, -120), (key508, -120), (key521, 120), (key628, 120), (key630, -120)]

def entry19_18 : Integer.Sparse Key := [(key1488, 120), (key1491, -120), (key1714, -120), (key1724, 120), (key1862, 120), (key1868, -120)]

def entry19_19 : Integer.Sparse Key := [(key291, 120), (key294, -120), (key518, -120), (key553, 192), (key631, 48), (key647, -120)]

def entry20_0 : Integer.Sparse Key := [(key2617, 24), (key2620, -24), (key2633, -24), (key2643, 36), (key2650, 12), (key2655, -24), (key2672, -24), (key2675, 24), (key2707, 36), (key2730, 84), (key2739, -24), (key2749, -96), (key2787, 12), (key2797, -24), (key2810, -24), (key2833, -96), (key2899, 24), (key2906, 60), (key2940, -12), (key2945, 24), (key2952, 24), (key2962, 96), (key2978, 12), (key2985, -96)]

def entry20_1 : Integer.Sparse Key := [(key1294, 120), (key1314, -120), (key1389, -120), (key1422, 120), (key1544, 120), (key1571, -120)]

def entry20_2 : Integer.Sparse Key := [(key2612, 48), (key2616, 48), (key2618, 16), (key2621, 8), (key2628, -60), (key2632, -36), (key2640, -8), (key2641, -24), (key2644, -24), (key2646, 8), (key2653, 16), (key2660, 8), (key2667, -48), (key2671, -48), (key2673, -12), (key2676, -12), (key2702, 72), (key2706, 60), (key2728, 24), (key2732, 24), (key2735, -12), (key2737, 12), (key2747, -24), (key2753, 12), (key2758, -24), (key2782, 36), (key2786, 24), (key2794, 12), (key2795, 12), (key2798, 12), (key2805, -60), (key2809, -36), (key2829, -8), (key2831, -24), (key2835, -24), (key2897, -12), (key2904, 12), (key2920, -12), (key2923, 12), (key2948, 8), (key2960, 16), (key2976, 12), (key2983, -12), (key3017, 8), (key3023, 12), (key3026, -12)]

def entry20_3 : Integer.Sparse Key := [(key1006, 120), (key1019, -120), (key1041, -120), (key1076, 120), (key1127, 120), (key1155, -120)]

def entry20_4 : Integer.Sparse Key := [(key2615, 120), (key2631, -120), (key2670, -120), (key2705, 120), (key2785, 120), (key2808, -120)]

def entry20_5 : Integer.Sparse Key := [(key1296, 24), (key1303, -24), (key1316, -24), (key1330, 24), (key1340, 24), (key1346, -24), (key1391, -24), (key1398, 24), (key1424, 24), (key1448, -24), (key1458, -24), (key1467, 24), (key1546, 24), (key1560, -24), (key1573, -24), (key1597, 24), (key1660, 24), (key1668, -24), (key1775, 96), (key1781, -96), (key1791, -96), (key1799, 96), (key1818, 96), (key1826, -96)]

def entry20_6 : Integer.Sparse Key := [(key2693, -16), (key2719, 24), (key2733, 120), (key2756, -24), (key2759, -120), (key2822, -24), (key2836, -120), (key2924, 96), (key3015, 24), (key3018, 104), (key3027, -96), (key3055, 16), (key3070, -24), (key3074, 24), (key3107, 24), (key3112, -24), (key3117, 16), (key3146, 24), (key3147, -24)]

def entry20_7 : Integer.Sparse Key := [(key1296, 96), (key1303, 24), (key1316, -96), (key1330, -24), (key1340, -24), (key1346, 24), (key1391, -96), (key1398, -24), (key1424, 96), (key1448, 24), (key1458, 24), (key1467, -24), (key1546, 96), (key1560, 24), (key1573, -96), (key1597, -24), (key1660, -24), (key1668, 24), (key1775, 24), (key1781, -24), (key1791, -24), (key1799, 24), (key1818, 24), (key1826, -24)]

def entry20_8 : Integer.Sparse Key := [(key1005, 120), (key1018, -120), (key1040, -120), (key1075, 120), (key1126, 120), (key1154, -120)]

def entry20_9 : Integer.Sparse Key := [(key2617, -24), (key2620, 24), (key2633, 24), (key2643, 96), (key2650, -24), (key2655, -96), (key2672, 24), (key2675, -24), (key2707, -24), (key2730, 36), (key2739, -24), (key2749, 36), (key2787, -24), (key2797, -48), (key2810, 24), (key2833, -36), (key2899, 96), (key2906, -12), (key2940, 12), (key2945, 36), (key2952, -12), (key2962, 24), (key2978, -60), (key2985, -24)]

def entry20_10 : Integer.Sparse Key := [(key2374, -24), (key2380, 48), (key2391, -60), (key2402, 24), (key2408, -48), (key2439, 60), (key2481, 48), (key2505, -48), (key2591, 24), (key2596, 72), (key2605, -60), (key2770, -24), (key2775, -72), (key2917, 72), (key3006, 60), (key3020, -72)]

def entry20_11 : Integer.Sparse Key := [(key2594, 120), (key2601, -120), (key2773, -120), (key2890, 120), (key2932, 120), (key2969, -120)]

def entry20_12 : Integer.Sparse Key := [(key2616, 96), (key2619, 24), (key2632, -96), (key2642, -24), (key2649, -24), (key2654, 24), (key2671, -96), (key2674, -24), (key2706, 96), (key2729, 24), (key2738, 24), (key2748, -24), (key2786, 96), (key2796, 24), (key2809, -96), (key2832, -24), (key2898, -24), (key2905, 24), (key2939, 24), (key2944, -24), (key2951, -24), (key2961, 24), (key2977, 24), (key2984, -24)]

def entry20_13 : Integer.Sparse Key := [(key2082, 120), (key2087, -120), (key2179, -120), (key2189, 120), (key2281, 120), (key2289, -120)]

def entry20_14 : Integer.Sparse Key := [(key2379, -12), (key2382, 48), (key2393, -72), (key2407, 12), (key2410, -48), (key2441, 72), (key2483, 48), (key2507, -48), (key2592, 12), (key2595, 72), (key2602, -48), (key2771, -12), (key2774, -72), (key2891, 72), (key2933, 48), (key2970, -72)]

def entry20_15 : Integer.Sparse Key := [(key2612, 12), (key2616, 12), (key2621, -24), (key2628, -12), (key2632, -12), (key2641, 12), (key2644, 24), (key2658, 12), (key2660, -24), (key2671, -24), (key2676, 24), (key2702, 12), (key2706, 24), (key2728, -12), (key2732, 96), (key2753, -24), (key2758, -96), (key2786, 12), (key2798, -24), (key2809, -24), (key2829, -8), (key2835, -96), (key2920, 24), (key2923, 60), (key2948, 8), (key2960, 16), (key2976, 36), (key2983, -36), (key3008, -12), (key3010, 24), (key3012, 24), (key3017, 80), (key3023, -24), (key3026, -60)]

def entry20_16 : Integer.Sparse Key := [(key2616, 48), (key2619, 72), (key2632, -48), (key2642, 48), (key2649, -72), (key2654, -48), (key2671, -48), (key2674, -72), (key2706, 48), (key2729, -48), (key2738, 72), (key2748, 48), (key2786, 48), (key2796, -48), (key2809, -48), (key2832, 48), (key2898, 48), (key2905, -48), (key2939, 72), (key2944, 48), (key2951, -72), (key2961, -48), (key2977, -48), (key2984, 48)]

def entry20_17 : Integer.Sparse Key := [(key1296, 24), (key1302, -24), (key1316, -24), (key1329, 24), (key1339, 24), (key1345, -24), (key1391, -24), (key1397, 24), (key1424, 24), (key1447, -24), (key1457, -24), (key1466, 24), (key1546, 24), (key1559, -24), (key1573, -24), (key1596, 24), (key1659, 24), (key1667, -24), (key1774, 96), (key1780, -96), (key1790, -96), (key1798, 96), (key1817, 96), (key1825, -96)]

def entry20_18 : Integer.Sparse Key := [(key2616, 24), (key2619, -24), (key2632, -24), (key2642, 24), (key2649, 24), (key2654, -24), (key2671, -24), (key2674, 24), (key2706, 24), (key2729, 96), (key2738, -24), (key2748, -96), (key2786, 24), (key2796, -24), (key2809, -24), (key2832, -96), (key2898, 24), (key2905, 96), (key2939, -24), (key2944, 24), (key2951, 24), (key2961, 96), (key2977, -24), (key2984, -96)]

def entry20_19 : Integer.Sparse Key := [(key1370, 120), (key1379, -120), (key1496, -120), (key1519, 120), (key1728, 120), (key1747, -120)]

def entry20_20 : Integer.Sparse Key := [(key2617, 72), (key2620, 48), (key2633, -72), (key2643, -96), (key2655, 48), (key2672, -72), (key2675, -48), (key2707, 96), (key2730, 96), (key2739, 48), (key2749, -96), (key2787, 48), (key2797, 48), (key2810, -72), (key2833, -96), (key2899, -48), (key2906, 48), (key2962, 48), (key2978, 48), (key2985, -48)]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row416 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 2), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row417 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 2), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row418 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row419 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row420 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row421 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row422 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row423 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row424 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row425 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row426 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row427 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row428 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row429 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row430 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row431 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row432 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row433 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row434 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row435 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row436 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row437 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row438 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row439 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row440 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row441 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row442 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row443 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row444 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row445 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row446 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row447 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row448 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row449 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row450 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row451 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row452 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row453 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row454 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row455 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row456 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row457 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row458 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row459 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row460 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row461 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row462 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row463 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row464 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row465 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row466 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row467 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row468 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row469 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row470 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row471 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row472 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row473 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row474 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row475 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row476 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row477 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row478 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row479 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row480 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row481 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row482 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row483 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row484 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row485 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row486 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row487 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row488 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row489 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row490 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row491 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row492 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row493 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row494 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row495 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row496 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row497 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row498 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row499 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row500 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row501 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row502 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row503 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row504 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row505 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row506 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row507 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row508 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row509 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row510 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row511 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row512 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row513 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row514 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row515 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row516 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row517 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row518 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row519 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row520 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row521 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row522 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row523 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row524 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row525 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row526 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row527 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row528 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row529 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row530 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row531 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row532 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row533 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row534 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row535 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row536 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row537 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row538 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row539 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row540 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row541 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row542 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row543 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row544 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row545 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row546 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row547 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row548 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

def row549 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row550 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row551 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row552 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row553 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

def row554 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row555 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row556 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row557 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row558 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

def row559 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row560 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row561 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row562 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row563 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

def row564 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row565 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row566 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row567 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row568 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row569 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row570 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row571 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row572 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row573 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row574 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row575 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row576 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row577 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row578 : Integer.Sparse Key := [(key1300, 2), (key1304, -2), (key1320, -2), (key1331, 2), (key1341, 2), (key1347, -2), (key1395, -2), (key1399, 2), (key1428, 2), (key1449, -2), (key1459, -2), (key1468, 2), (key1550, 2), (key1561, -2), (key1577, -2), (key1598, 2), (key1661, 2), (key1669, -2), (key1776, -2), (key1782, 2), (key1792, 2), (key1800, -2), (key1819, -2), (key1827, 2)]

def row579 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row580 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row581 : Integer.Sparse Key := [(key1300, -2), (key1304, 2), (key1320, 2), (key1331, -2), (key1341, -2), (key1347, 2), (key1395, 2), (key1399, -2), (key1428, -2), (key1449, 2), (key1459, 2), (key1468, -2), (key1550, -2), (key1561, 2), (key1577, 2), (key1598, -2), (key1661, -2), (key1669, 2), (key1776, 2), (key1782, -2), (key1792, -2), (key1800, 2), (key1819, 2), (key1827, -2)]

def row582 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row583 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row584 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row585 : Integer.Sparse Key := [(key1300, 1), (key1304, -1), (key1320, -1), (key1331, 1), (key1341, 1), (key1347, -1), (key1395, -1), (key1399, 1), (key1428, 1), (key1449, -1), (key1459, -1), (key1468, 1), (key1550, 1), (key1561, -1), (key1577, -1), (key1598, 1), (key1661, 1), (key1669, -1), (key1776, -1), (key1782, 1), (key1792, 1), (key1800, -1), (key1819, -1), (key1827, 1)]

def row586 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row587 : Integer.Sparse Key := [(key1300, -1), (key1304, 1), (key1320, 1), (key1331, -1), (key1341, -1), (key1347, 1), (key1395, 1), (key1399, -1), (key1428, -1), (key1449, 1), (key1459, 1), (key1468, -1), (key1550, -1), (key1561, 1), (key1577, 1), (key1598, -1), (key1661, -1), (key1669, 1), (key1776, 1), (key1782, -1), (key1792, -1), (key1800, 1), (key1819, 1), (key1827, -1)]

def row588 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row589 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row590 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, 2), (key2790, -2), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2935, -2), (key2941, 2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row591 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row592 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row593 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row594 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row595 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, -2), (key2790, 2), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2935, 2), (key2941, -2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

def row596 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row597 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row598 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row599 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row600 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -4), (key2722, 4), (key2734, 4), (key2745, -4), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

def row601 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row602 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row603 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row604 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row605 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 4), (key2722, -4), (key2734, -4), (key2745, 4), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row606 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row607 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -2), (key2722, 2), (key2734, 2), (key2745, -2), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row608 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row609 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row610 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, 1), (key2722, -2), (key2745, 1), (key2778, 2), (key2781, -1), (key2790, -2), (key2801, -1), (key2825, 2), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2941, 1), (key2958, -1), (key2971, -1), (key2981, 1)]

def row611 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, 1), (key2722, -2), (key2745, 1), (key2778, 2), (key2781, -1), (key2790, -2), (key2801, -1), (key2825, 2), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2941, 1), (key2958, -1), (key2971, -1), (key2981, 1)]

def row612 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -2), (key2734, 1), (key2745, 2), (key2778, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row613 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -2), (key2734, 1), (key2745, 2), (key2778, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row614 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, 2), (key2734, -1), (key2745, -2), (key2778, -1), (key2781, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row615 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, 2), (key2734, -1), (key2745, -2), (key2778, -1), (key2781, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row616 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2701, -1), (key2722, 3), (key2745, -1), (key2778, -2), (key2781, 1), (key2790, 2), (key2801, 1), (key2825, -2), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2958, 1), (key2971, 1), (key2974, 1), (key2981, -1)]

def row617 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2701, -1), (key2722, 3), (key2745, -1), (key2778, -2), (key2781, 1), (key2790, 2), (key2801, 1), (key2825, -2), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2958, 1), (key2971, 1), (key2974, 1), (key2981, -1)]

def row618 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 2), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -1), (key2722, -2), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, 1), (key2902, -1), (key2941, 1), (key2947, -1), (key2958, -1), (key2971, 1), (key2974, -1), (key2981, 1)]

def row619 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 2), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -1), (key2722, -2), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, 1), (key2902, -1), (key2941, 1), (key2947, -1), (key2958, -1), (key2971, 1), (key2974, -1), (key2981, 1)]

def row620 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, 2), (key2790, -2), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2935, -2), (key2941, 2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row621 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row622 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row623 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2790, 2), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2935, 2), (key2941, -2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

def row624 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row625 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row626 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 2), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row627 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 2), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

def row628 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row629 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row630 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

def row631 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

def row632 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

def row633 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row634 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row635 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2899, -1), (key2915, -1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row636 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2899, -1), (key2915, -1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row637 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row638 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

def row639 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row640 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

def row641 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

def row642 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row643 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row644 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2751, 1), (key2797, -1), (key2915, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row645 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2751, 1), (key2797, -1), (key2915, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row646 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row647 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, 1), (key2797, -1), (key2915, -1), (key2945, -1), (key2962, -1), (key2964, 1), (key2978, 1), (key2985, 1), (key2994, -3), (key3004, 2)]

def row648 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row649 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row650 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row651 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1764 : Integer.Sparse Key := [(key2402, -2), (key2408, 2), (key2468, 2), (key2481, -2), (key2537, -2), (key2542, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row308 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row309 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row310 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row311 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row312 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row313 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row314 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

def row315 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row316 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row317 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

def row318 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row319 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row320 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row321 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row322 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row323 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row324 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row325 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row326 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row327 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row328 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row329 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row330 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row331 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row332 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row333 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

def row334 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row335 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

def row336 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

def row337 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row338 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row339 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

def row340 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row341 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row342 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row343 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row344 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row345 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row346 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

def row347 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row348 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row349 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

def row350 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row351 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row352 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row353 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row354 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row355 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row356 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

def row357 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row358 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row359 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

def row360 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row361 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row362 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row363 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row364 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row365 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row366 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row367 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row368 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row369 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row370 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row371 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row372 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row373 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row374 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row375 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

def row376 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row377 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

def row378 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -2), (key270, -2), (key275, 2), (key309, 2), (key311, -2), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key392, -2), (key403, 2), (key413, 2), (key424, -2), (key473, -2), (key479, 2), (key571, 2), (key576, -2), (key581, -2), (key587, 2), (key599, 2), (key605, -2)]

def row379 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row380 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row381 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 4), (key275, -2), (key309, -2), (key311, 2), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key392, 2), (key403, -2), (key413, -2), (key424, 2), (key473, 2), (key479, -2), (key571, -2), (key576, 2), (key581, 2), (key587, -2), (key599, -2), (key605, 2)]

def row382 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row383 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row384 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row385 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row386 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row387 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

def row388 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 2), (key270, 2), (key275, -2), (key309, -2), (key311, 2), (key323, 4), (key334, -4), (key338, -4), (key344, 4), (key413, -2), (key424, 2), (key473, 2), (key479, -2), (key581, 2), (key587, -2), (key599, -2), (key605, 2)]

def row389 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row390 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row391 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -2), (key270, -2), (key275, 2), (key309, 2), (key311, -2), (key323, -4), (key334, 4), (key338, 4), (key344, -4), (key413, 2), (key424, -4), (key473, -2), (key479, 2), (key587, 2), (key599, 2), (key605, -2)]

def row392 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key587, -1), (key599, -1), (key605, 1)]

def row393 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key587, -1), (key599, -1), (key605, 1)]

def row394 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key473, 1), (key479, -1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row395 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key413, -1), (key473, 1), (key479, -1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row396 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row397 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

def row398 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -4), (key275, 2), (key309, 2), (key311, -2), (key323, -2), (key334, 4), (key344, -2), (key392, -2), (key403, 4), (key413, 2), (key424, -4), (key473, -2), (key479, 2), (key576, -2), (key587, 2), (key599, 2), (key605, -2)]

def row399 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row400 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row401 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 4), (key275, -2), (key309, -2), (key311, 2), (key323, 2), (key334, -4), (key344, 4), (key392, 2), (key403, -4), (key413, -2), (key424, 4), (key473, 2), (key479, -2), (key587, -2), (key599, -2), (key605, 2)]

def row402 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key344, -2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key587, 1), (key599, 1), (key605, -1)]

def row403 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key344, -2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key587, 1), (key599, 1), (key605, -1)]

def row404 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key576, -2), (key587, 1), (key599, 1), (key605, -1)]

def row405 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 2), (key392, -1), (key403, 2), (key413, 1), (key424, -2), (key473, -1), (key479, 1), (key576, -2), (key587, 1), (key599, 1), (key605, -1)]

def row406 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row407 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -2), (key344, 1), (key392, 1), (key403, -2), (key413, -1), (key424, 2), (key473, 1), (key479, -1), (key576, 1), (key587, -1), (key599, -1), (key605, 1)]

def row408 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key270, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key338, -2), (key344, 1), (key392, 1), (key413, -1), (key473, 1), (key479, -1), (key571, -2), (key576, 1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row409 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key270, 2), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key338, -2), (key344, 1), (key392, 1), (key413, -1), (key473, 1), (key479, -1), (key571, -2), (key576, 1), (key581, 2), (key587, -1), (key599, -1), (key605, 1)]

def row410 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key392, -1), (key403, 2), (key413, 1), (key424, -1), (key473, -1), (key571, 1), (key576, -2), (key581, -1), (key587, 1), (key599, 2), (key605, -1)]

def row411 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key392, -1), (key403, 2), (key413, 1), (key424, -1), (key473, -1), (key571, 1), (key576, -2), (key581, -1), (key587, 1), (key599, 2), (key605, -1)]

def row412 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key338, 1), (key344, -1), (key403, 1), (key413, 1), (key473, -1), (key479, 1), (key571, 2), (key576, -1), (key581, -2), (key587, 1), (key599, 1), (key605, -1)]

def row413 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key270, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -2), (key338, 1), (key344, -1), (key403, 1), (key413, 1), (key473, -1), (key479, 1), (key571, 2), (key576, -1), (key581, -2), (key587, 1), (key599, 1), (key605, -1)]

def row414 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -1), (key338, -1), (key344, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -2), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key605, 1)]

def row415 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 2), (key334, -1), (key338, -1), (key344, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -2), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key605, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1153 : Sparse Master := [(Sum.inr 1153, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


