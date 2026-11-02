-- Prove2me | Definitions.Def_OAIQ106D090
-- name    : OAIQ106D090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:57:45.991292+00:00
-- url     : https://prove2.me/theorems/bccfeea4-69ff-48d1-9511-dbead211571a
-- title:
--   Definitions bundle OAIQ106D090 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1855 declarations of OpenAI's Lean: 1855 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry11_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entry12_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entry13_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entry14_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entry14_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entry14_10` and 1815 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block3Data`, `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block17`, `MutuallyUnbiased_GramKeys_Block18`, `MutuallyUnbiased_GramKeys_Block19`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block20`, `MutuallyUnbiased_GramKeys_Block21`, `MutuallyUnbiased_GramKeys_Block22`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block24`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block6`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block100`, `MutuallyUnbiased_GramRows_Block75`, `MutuallyUnbiased_GramRows_Block76`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_GramRows_Block82`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block91`, `MutuallyUnbiased_GramRows_Block92`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_GramRows_Block94`, `MutuallyUnbiased_GramRows_Block95`, `MutuallyUnbiased_GramRows_Block96`, `MutuallyUnbiased_GramRows_Block97`, `MutuallyUnbiased_GramRows_Block98`, `MutuallyUnbiased_MixedSemantics_Values15`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D144`, `OAIQ106D146`, `OAIQ106D147`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D155`, `OAIQ106D156`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D162`, `OAIQ106D163`, `OAIQ106D164`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D167`, `OAIQ106D168`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172`, `OAIQ106D173`, `OAIQ106D174`, `OAIQ106D175`, `OAIQ106D176`, `OAIQ106D177`, `OAIQ106D178`, `OAIQ106D179`, `OAIQ106D180`, `OAIQ106D181`, `OAIQ106D182`, `OAIQ106D183`, `OAIQ106D184`, `OAIQ106D185` and `OAIQ106D186`.
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

def key0 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key3 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key9 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key11 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key14 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key24 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key30 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key36 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key49 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key75 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key83 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key86 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key88 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key90 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key91 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key92 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key94 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key97 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key102 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key106 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key110 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key116 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key118 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (1, 0), (1, 0), (1, 2)]⟩

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

def key138 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key146 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key147 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩
def key152 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩
def key153 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩
def key154 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩
def key155 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key156 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩
def key161 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩
def key162 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩
def key165 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key167 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key187 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩
def key194 : Key := ⟨0, 0, [(-3, 2), (0, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩
def key203 : Key := ⟨0, 0, [(-3, 2), (0, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩
def key204 : Key := ⟨0, 0, [(-3, 2), (0, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key219 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key227 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key232 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key233 : Key := ⟨0, 0, [(-2, -3), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩

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

def key1285 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key1286 : Key := ⟨0, 1, [(-2, -3), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key1357 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key1359 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key1368 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key1371 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key1377 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 0), (0, 3), (1, -1), (1, 0)]⟩
def key1380 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0)]⟩
def key1402 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key1407 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩

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

def key1408 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key1411 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key1430 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
def key1431 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 1), (3, 2)]⟩
def key1435 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
def key1436 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key1437 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -1)]⟩
def key1461 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (0, 0), (3, 2)]⟩
def key1462 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩
def key1463 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩
def key1483 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key1484 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key1485 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key1489 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key1494 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key1497 : Key := ⟨0, 1, [(-2, -1), (0, -2), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key1498 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 0), (0, 0), (2, 3)]⟩
def key1505 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, -1), (0, 3), (1, 0), (1, 0)]⟩
def key1508 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key1510 : Key := ⟨0, 1, [(-2, -1), (0, -1), (0, 1), (0, 2), (1, -1), (1, 0)]⟩
def key1516 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 3), (1, -2), (1, 0)]⟩
def key1517 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 0), (0, 3), (1, -1), (1, -1)]⟩
def key1520 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0)]⟩
def key1522 : Key := ⟨0, 1, [(-2, -1), (0, 1), (0, 1), (0, 1), (1, -2), (1, 0)]⟩
def key1523 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key1528 : Key := ⟨0, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩

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

def key1579 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
def key1580 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 1), (3, 2)]⟩
def key1585 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key1586 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩
def key1601 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 3)]⟩
def key1602 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 1), (3, 2)]⟩
def key1603 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 2), (3, 1)]⟩
def key1606 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 3), (2, 0)]⟩
def key1610 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 2), (2, 0)]⟩
def key1612 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 1), (2, 0)]⟩
def key1613 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 3)]⟩
def key1614 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 1), (3, 2)]⟩
def key1615 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 2), (3, 1)]⟩
def key1619 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 3), (2, 0)]⟩
def key1627 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 3)]⟩
def key1628 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, 3), (2, -1)]⟩
def key1663 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (0, -1), (3, 2)]⟩

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

def key1664 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, 2), (2, -1)]⟩
def key1695 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key1696 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key1697 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key1700 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key1702 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key1704 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key1705 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key1707 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key1708 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key1709 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 0), (2, 3)]⟩
def key1710 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 1), (2, 2)]⟩
def key1711 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 2), (2, 1)]⟩
def key1715 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (0, 1), (2, 1)]⟩
def key1717 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 1), (1, 0), (1, 2)]⟩
def key1719 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 2), (1, 0), (1, 1)]⟩
def key1720 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 3), (1, 0), (1, 0)]⟩
def key1726 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 0), (0, 3), (1, -1), (1, 0)]⟩
def key1729 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, 1), (0, 2), (1, -1), (1, 0)]⟩
def key1730 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 0), (2, 3)]⟩
def key1731 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, -1), (0, 1), (2, 2)]⟩
def key1738 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, -1), (0, 3), (1, -1), (1, 0)]⟩
def key1744 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 3), (1, -2), (1, 0)]⟩
def key1745 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 0), (0, 3), (1, -1), (1, -1)]⟩
def key1748 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 2), (1, -2), (1, 0)]⟩
def key1749 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 2), (1, -1), (1, -1)]⟩
def key1754 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -3), (1, 0)]⟩
def key1755 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -2), (1, -1)]⟩
def key1758 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -3), (1, 0)]⟩
def key1759 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1)]⟩
def key1760 : Key := ⟨0, 1, [(-2, 0), (0, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩
def key1761 : Key := ⟨0, 1, [(-2, 0), (0, 1), (0, 1), (0, 1), (1, -2), (1, -1)]⟩

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

def key1794 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 2)]⟩
def key1795 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩
def key1821 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 2)]⟩
def key1822 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, -1)]⟩
def key1838 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (0, -1), (0, 0), (3, 1)]⟩
def key1850 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key1851 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key1852 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key1855 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key1857 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 0), (0, 2), (1, 0), (1, 0)]⟩
def key1858 : Key := ⟨0, 1, [(-2, 1), (0, -3), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key1859 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 0), (2, 2)]⟩
def key1861 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 2), (2, 0)]⟩
def key1864 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 1), (0, 1), (2, 0)]⟩
def key1866 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, -1), (0, 2), (1, 0), (1, 0)]⟩
def key1867 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key1869 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 1), (0, 1), (2, -1)]⟩
def key1871 : Key := ⟨0, 1, [(-2, 1), (0, -2), (0, 0), (0, 2), (1, -1), (1, 0)]⟩
def key1873 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, -1), (0, 0), (2, 2)]⟩
def key1876 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, -1), (0, 2), (1, -1), (1, 0)]⟩
def key1877 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩
def key1881 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 2), (1, -2), (1, 0)]⟩
def key1882 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 2), (1, -1), (1, -1)]⟩
def key1883 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 1), (0, 1), (1, -2), (1, 0)]⟩
def key1884 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 0), (0, 2), (2, -3)]⟩
def key1886 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 1), (0, 1), (2, -3)]⟩
def key1888 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 2), (1, -3), (1, 0)]⟩
def key1889 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 0), (0, 2), (1, -2), (1, -1)]⟩
def key1890 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 1), (0, 1), (1, -3), (1, 0)]⟩
def key1891 : Key := ⟨0, 1, [(-2, 1), (0, 0), (0, 1), (0, 1), (1, -2), (1, -1)]⟩

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

def key1932 : Key := ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 0), (0, 0), (2, 1)]⟩
def key1933 : Key := ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 0), (0, 1), (2, 0)]⟩
def key1935 : Key := ⟨0, 1, [(-2, 2), (0, -3), (0, 0), (0, 1), (1, 0), (1, 0)]⟩
def key1936 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 0), (0, 0), (2, 1)]⟩
def key1937 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩
def key1939 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩
def key1940 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩
def key1942 : Key := ⟨0, 1, [(-2, 2), (0, -2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩
def key1943 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, -1), (0, 0), (2, 1)]⟩
def key1944 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, -1), (0, -1), (0, 1), (2, 0)]⟩
def key1951 : Key := ⟨0, 1, [(-2, 2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0)]⟩
def key1953 : Key := ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 0), (0, 1), (2, -3)]⟩
def key1955 : Key := ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -3), (1, 0)]⟩
def key1956 : Key := ⟨0, 1, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -2), (1, -1)]⟩
def key1957 : Key := ⟨0, 1, [(-2, 3), (0, -3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩
def key1958 : Key := ⟨0, 1, [(-2, 3), (0, -2), (0, -1), (0, 0), (0, 0), (2, 0)]⟩
def key1960 : Key := ⟨0, 1, [(-2, 3), (0, -2), (0, 0), (0, 0), (0, 0), (2, -1)]⟩
def key1962 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, -1), (0, 0), (2, 0)]⟩
def key1964 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, -1), (0, 0), (0, 0), (2, -1)]⟩
def key1966 : Key := ⟨0, 1, [(-2, 3), (0, -1), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key1969 : Key := ⟨0, 1, [(-2, 3), (0, 0), (0, 0), (0, 0), (0, 0), (2, -3)]⟩
def key2009 : Key := ⟨0, 1, [(-1, -3), (-1, 3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩

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

def key2197 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -1), (0, -1), (0, 0), (2, 1)]⟩
def key2198 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -1), (0, -1), (0, 1), (2, 0)]⟩
def key2204 : Key := ⟨0, 1, [(-1, -1), (-1, 3), (0, -1), (0, -1), (0, 0), (2, 0)]⟩
def key2205 : Key := ⟨0, 1, [(-1, -1), (-1, 3), (0, -1), (0, 0), (0, 0), (2, -1)]⟩
def key2269 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 2), (2, 0)]⟩
def key2272 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 1), (0, 1), (2, 0)]⟩
def key2276 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 2), (2, 0)]⟩
def key2300 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -3), (0, 0), (0, 1), (2, 0)]⟩
def key2303 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 1), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2308 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, -1), (2, 1)]⟩
def key2309 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, -1), (0, 1), (2, -1)]⟩
def key2316 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, -3), (0, 0), (0, 0), (2, 0)]⟩
def key2317 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, -2), (0, -1), (0, 0), (2, 0)]⟩
def key2319 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, -1), (0, -1), (0, -1), (2, 0)]⟩
def key2320 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, -1), (0, -1), (0, 0), (2, -1)]⟩
def key2322 : Key := ⟨0, 1, [(-1, 0), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -3)]⟩
def key2323 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 1)]⟩
def key2327 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, -1), (0, 0), (2, 1)]⟩
def key2351 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2352 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2355 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2360 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2368 : Key := ⟨1, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2396 : Key := ⟨1, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2412 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key2413 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key2415 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key2416 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key2417 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key2418 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key2420 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key2422 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩
def key2423 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2424 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key2427 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key2429 : Key := ⟨1, 1, [(-3, -1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2438 : Key := ⟨1, 1, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key2446 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2447 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2450 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2451 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 0), (2, 2)]⟩
def key2453 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key2454 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key2455 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2459 : Key := ⟨1, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key2462 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key2463 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key2466 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key2469 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key2471 : Key := ⟨1, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key2485 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
def key2486 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩
def key2488 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩
def key2489 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
def key2490 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩
def key2491 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key2492 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, -1), (2, 2)]⟩
def key2493 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩
def key2495 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 0), (1, 3)]⟩
def key2504 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key2508 : Key := ⟨1, 1, [(-3, 0), (0, -1), (0, 1), (1, -1), (1, -1), (1, 2)]⟩
def key2511 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, -3), (2, 3)]⟩
def key2512 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩
def key2516 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩
def key2518 : Key := ⟨1, 1, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩
def key2546 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩
def key2547 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩
def key2548 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩
def key2549 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩
def key2550 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩
def key2556 : Key := ⟨1, 1, [(-3, 1), (0, -1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩

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

def key284 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key286 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key287 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key288 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key289 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key293 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key297 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 3), (1, -1), (1, 0)]⟩
def key298 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key299 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0)]⟩
def key348 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key355 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key356 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key362 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key366 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key370 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩
def key372 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 3), (1, -2), (1, 0)]⟩
def key377 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩

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

def key2581 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2585 : Key := ⟨1, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2677 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key2678 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key2680 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, 1)]⟩
def key2681 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key2682 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 1), (1, 0), (2, 2)]⟩
def key2683 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key2687 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, -1), (2, 3)]⟩

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

def key2688 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key2689 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, -1), (2, 2)]⟩
def key2692 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key2694 : Key := ⟨1, 1, [(-2, -1), (-1, -1), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key2708 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
def key2709 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 0), (2, 3)]⟩
def key2711 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, 1)]⟩
def key2712 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
def key2713 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (2, 3)]⟩
def key2714 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key2715 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, -1), (2, 2)]⟩
def key2716 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, 2), (2, -1)]⟩
def key2718 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, -1), (1, -1), (1, 0), (1, 3)]⟩
def key2731 : Key := ⟨1, 1, [(-2, -1), (-1, 0), (0, 1), (1, -1), (1, -1), (1, 2)]⟩
def key2740 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (1, 0), (2, 2)]⟩
def key2741 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩
def key2742 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩
def key2743 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩
def key2744 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩
def key2750 : Key := ⟨1, 1, [(-2, -1), (-1, 1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩
def key2760 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key2761 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 0), (2, 3)]⟩
def key2764 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key2769 : Key := ⟨1, 1, [(-2, 0), (-1, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key2811 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
def key2812 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 0), (2, 3)]⟩
def key2814 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 2), (2, 1)]⟩
def key2815 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩

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

def key2816 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, -1), (2, 3)]⟩
def key2817 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key2818 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, -1), (2, 2)]⟩
def key2819 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩
def key2830 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key2834 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, 1), (1, -1), (1, -1), (1, 2)]⟩
def key2837 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 3)]⟩
def key2838 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 0), (2, 3)]⟩
def key2841 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 3), (2, 0)]⟩
def key2844 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 2), (2, 0)]⟩
def key2846 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -3), (1, 0), (1, 0), (1, 3)]⟩
def key2849 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 3)]⟩
def key2850 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 3)]⟩
def key2853 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 3), (2, 0)]⟩
def key2861 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (0, -1), (3, 3)]⟩
def key2862 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, -1), (2, 3)]⟩
def key2863 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, 3), (2, -1)]⟩
def key2871 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, -1), (1, -1), (1, -1), (1, 3)]⟩
def key2872 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, -3), (2, 3)]⟩
def key2873 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩
def key2877 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩
def key2879 : Key := ⟨1, 1, [(-2, 0), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩
def key2900 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, -1), (2, 2)]⟩
def key2901 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, 2), (2, -1)]⟩
def key2907 : Key := ⟨1, 1, [(-2, 0), (-1, 1), (0, -1), (1, -1), (1, -1), (1, 2)]⟩

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

def key2954 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩
def key2955 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, -1), (2, 2)]⟩
def key2956 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩
def key2963 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩
def key2979 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, -1), (2, 2)]⟩
def key2980 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, 2), (2, -1)]⟩
def key2986 : Key := ⟨1, 1, [(-2, 1), (-1, 0), (0, -1), (1, -1), (1, -1), (1, 2)]⟩
def key3035 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 0), (0, 1), (1, 0), (2, 2)]⟩
def key3039 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, 2)]⟩
def key3045 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 0), (3, 3)]⟩
def key3050 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 1), (1, 0), (2, 2)]⟩
def key3054 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 0), (2, 2)]⟩
def key3059 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩
def key3060 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, -1), (1, 0), (2, 3)]⟩
def key3064 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 0), (1, -1), (2, 3)]⟩
def key3066 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 0), (0, 1), (1, -1), (2, 2)]⟩

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

def key3072 : Key := ⟨1, 1, [(-1, -2), (-1, 0), (-1, 1), (0, 0), (1, -1), (2, 2)]⟩
def key3079 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 0), (0, 0), (3, 3)]⟩
def key3082 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, -1), (0, 1), (1, 0), (2, 2)]⟩
def key3084 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (3, 3)]⟩
def key3085 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, -1), (1, 0), (2, 3)]⟩
def key3087 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 0), (1, -1), (2, 3)]⟩
def key3088 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 0), (0, 1), (1, -1), (2, 2)]⟩
def key3091 : Key := ⟨1, 1, [(-1, -1), (-1, -1), (-1, 1), (0, 0), (1, -1), (2, 2)]⟩
def key3094 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (0, 0), (3, 3)]⟩
def key3095 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -2), (1, 0), (2, 3)]⟩
def key3099 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, -1), (0, -1), (3, 3)]⟩
def key3101 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 0), (1, -2), (2, 3)]⟩
def key3103 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 0), (0, 1), (1, -2), (2, 2)]⟩
def key3110 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 0), (1, -2), (2, 2)]⟩
def key3118 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (0, 0), (3, 3)]⟩
def key3119 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -3), (1, 0), (2, 3)]⟩
def key3122 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (0, -1), (3, 3)]⟩
def key3123 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -2), (1, -1), (2, 3)]⟩
def key3125 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, -1), (1, -2), (2, 3)]⟩
def key3127 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 0), (1, -3), (2, 3)]⟩
def key3128 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 0), (0, 1), (1, -3), (2, 2)]⟩
def key3138 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, 0), (1, -3), (2, 2)]⟩

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

def key395 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key428 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (1, 3), (2, 0)]⟩
def key430 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 1)]⟩
def key437 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 3), (2, 0)]⟩
def key440 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, 0), (1, 2), (2, 0)]⟩
def key461 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 1), (0, 1), (1, 1), (2, -3)]⟩
def key491 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key498 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key499 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key501 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 3), (1, 0), (1, 0)]⟩
def key503 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key504 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 1), (0, 2), (1, 0), (1, 0)]⟩
def key505 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 0), (2, 3)]⟩
def key510 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 1), (1, 0), (1, 2)]⟩

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

def key512 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 3), (1, 0), (1, 0)]⟩
def key513 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key514 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key519 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key522 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key524 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 2), (1, 0), (1, 0)]⟩
def key525 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 3), (1, -1), (1, 0)]⟩
def key526 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 1), (0, 2), (1, -1), (1, 0)]⟩
def key542 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 1), (1, -2), (1, 2)]⟩
def key545 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 3), (1, -2), (1, 0)]⟩
def key546 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 1), (0, 2), (1, -2), (1, 0)]⟩
def key555 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 2), (1, -2), (1, 0)]⟩
def key557 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -3), (1, 0)]⟩
def key558 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 3), (1, -2), (1, -1)]⟩
def key560 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩
def key561 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 1), (1, -2), (1, 0)]⟩
def key562 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -3), (1, 0)]⟩
def key563 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1)]⟩
def key564 : Key := ⟨0, 0, [(-2, 0), (0, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩
def key612 : Key := ⟨0, 0, [(-2, 1), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 0)]⟩
def key615 : Key := ⟨0, 0, [(-2, 1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -3)]⟩
def key617 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 0), (2, 2)]⟩
def key618 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key619 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 0), (0, 2), (2, 0)]⟩
def key622 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key623 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key625 : Key := ⟨0, 0, [(-2, 1), (0, -3), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key627 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 2), (2, 0)]⟩
def key629 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 0), (0, 2), (2, -1)]⟩
def key632 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, 0), (0, 1), (1, 0), (1, 0)]⟩

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

def key645 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 0), (0, 2), (2, -3)]⟩
def key649 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -3), (1, 1)]⟩
def key650 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (1, -2), (1, 0)]⟩
def key653 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 1), (0, 1), (1, -3), (1, 0)]⟩
def key666 : Key := ⟨0, 0, [(-2, 2), (0, -3), (0, 0), (0, 1), (1, 0), (1, 0)]⟩
def key669 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩
def key670 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 0), (0, 0), (2, 0)]⟩
def key673 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩
def key679 : Key := ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0)]⟩
def key680 : Key := ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key683 : Key := ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -3), (1, 0)]⟩
def key684 : Key := ⟨0, 0, [(-2, 2), (0, 0), (0, 0), (0, 1), (1, -2), (1, -1)]⟩
def key685 : Key := ⟨0, 0, [(-2, 3), (0, -3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩
def key686 : Key := ⟨0, 0, [(-2, 3), (0, -2), (0, -1), (0, 0), (0, 0), (2, 0)]⟩
def key687 : Key := ⟨0, 0, [(-2, 3), (0, -2), (0, 0), (0, 0), (0, 0), (2, -1)]⟩
def key692 : Key := ⟨0, 0, [(-2, 3), (0, 0), (0, 0), (0, 0), (0, 0), (2, -3)]⟩
def key714 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key718 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key724 : Key := ⟨0, 0, [(-1, -3), (-1, 3), (0, 0), (0, 0), (0, 0), (2, 0)]⟩
def key732 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key734 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 1), (0, 1), (2, 0)]⟩
def key750 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 0), (0, 0), (2, 0)]⟩

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

def key803 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (0, 2), (2, 0)]⟩
def key866 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 1), (2, 1)]⟩
def key868 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 1), (0, 1), (2, 0)]⟩
def key882 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 0), (0, 1), (0, 1), (2, -2)]⟩
def key891 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 1)]⟩
def key892 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (0, 2), (2, 0)]⟩
def key895 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 1), (0, 1), (2, 0)]⟩

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

def key898 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, -1), (0, 2), (2, 0)]⟩
def key901 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (0, 1), (2, 0)]⟩
def key916 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 1), (0, 1), (2, -3)]⟩
def key927 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 0), (0, 0), (2, 0)]⟩
def key942 : Key := ⟨0, 0, [(-1, 0), (-1, 3), (0, -3), (0, 0), (0, 0), (2, 0)]⟩
def key943 : Key := ⟨0, 0, [(-1, 0), (-1, 3), (0, -2), (0, -1), (0, 0), (2, 0)]⟩
def key946 : Key := ⟨0, 0, [(-1, 0), (-1, 3), (0, 0), (0, 0), (0, 0), (2, -3)]⟩
def key947 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 0), (2, 1)]⟩
def key948 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 0), (0, 1), (2, 0)]⟩
def key955 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (0, 1), (2, -3)]⟩
def key968 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key969 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key970 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key973 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key974 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key981 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key985 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key987 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key989 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key991 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key996 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1002 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key1016 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 0), (1, 3)]⟩

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

def key1024 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key1025 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1026 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1031 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1037 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key1045 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key1050 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key1052 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key1055 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key1058 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key1064 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key1065 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key1072 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 0), (1, 3)]⟩
def key1074 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key1082 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key1083 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 1), (3, 2)]⟩
def key1084 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (0, 2), (3, 1)]⟩
def key1087 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 0), (1, 3), (2, 0)]⟩
def key1088 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (0, 1), (3, 1)]⟩
def key1091 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 1), (1, 2), (2, 0)]⟩
def key1093 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (0, 2), (1, 1), (2, 0)]⟩
def key1094 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 0), (1, 3)]⟩
def key1095 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key1098 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key1099 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key1101 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key1102 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩
def key1103 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 1), (3, 2)]⟩
def key1104 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 2), (3, 1)]⟩
def key1108 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 3), (2, 0)]⟩
def key1109 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (0, 1), (3, 1)]⟩
def key1112 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩
def key1114 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key1115 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 0), (1, 3)]⟩
def key1124 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 0), (1, 3)]⟩
def key1131 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (0, 0), (3, 3)]⟩
def key1132 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (0, 1), (3, 2)]⟩
def key1136 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
def key1138 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 0), (1, 3), (2, -1)]⟩
def key1140 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (0, 1), (1, 2), (2, -1)]⟩
def key1143 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 0), (1, 3)]⟩
def key1144 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩
def key1151 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 0), (1, 3)]⟩

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

def key1153 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key1158 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (1, -1), (1, -1), (1, 2)]⟩
def key1160 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (0, 0), (1, 3), (2, -3)]⟩
def key1165 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 0), (1, 3)]⟩
def key1166 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (1, -3), (1, 1), (1, 2)]⟩
def key1167 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 0), (1, -2), (1, -1), (1, 3)]⟩
def key1170 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 0), (1, 2)]⟩
def key1172 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩
def key1173 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 2), (1, -3), (1, 0), (1, 1)]⟩
def key1177 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (0, 0), (3, 2)]⟩
def key1178 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (0, 1), (3, 1)]⟩
def key1180 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key1184 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩
def key1187 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (0, 0), (3, 2)]⟩
def key1188 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (0, 1), (3, 1)]⟩
def key1190 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key1194 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key1200 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key1203 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (0, 0), (3, 2)]⟩
def key1205 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, -1), (1, 2), (2, 0)]⟩
def key1207 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (0, 0), (1, 2), (2, -1)]⟩
def key1208 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩
def key1213 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key1215 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (1, -1), (1, -1), (1, 2)]⟩
def key1221 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩
def key1223 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key1226 : Key := ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (0, 0), (0, 0), (3, 1)]⟩
def key1229 : Key := ⟨0, 1, [(-3, 2), (0, -3), (0, 0), (1, 0), (1, 0), (1, 1)]⟩
def key1230 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (0, 0), (0, 0), (3, 1)]⟩
def key1246 : Key := ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (1, -3), (1, 0), (1, 1)]⟩
def key1248 : Key := ⟨0, 1, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key1272 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key1273 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key1274 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key1277 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization

def entry1_0 : Integer.Sparse Key := [(key1088, -720), (key1178, 720)]

def entry1_1 : Integer.Sparse Key := [(key0, 720), (key83, -720)]

def entry2_0 : Integer.Sparse Key := [(key976, 48), (key984, -48), (key1090, -288), (key1098, -240), (key1169, -192), (key1180, 240), (key1183, 288), (key1220, 192)]

def entry2_1 : Integer.Sparse Key := [(key3, 720), (key86, -720)]

def entry2_2 : Integer.Sparse Key := [(key1, 192), (key7, 528), (key84, -192), (key90, -480), (key151, -160), (key193, 64), (key202, 48)]

def entry3_0 : Integer.Sparse Key := [(key2377, -192), (key2389, 192), (key2405, -48), (key2436, 48), (key2471, -240), (key2479, 288), (key2502, -288), (key2518, 240)]

def entry3_1 : Integer.Sparse Key := [(key1024, 720), (key1102, -720)]

def entry3_2 : Integer.Sparse Key := [(key995, -48), (key1011, 48), (key1030, 528), (key1067, 192), (key1108, -480), (key1119, -48), (key1146, -192)]

def entry3_3 : Integer.Sparse Key := [(key2606, 192), (key2622, -192), (key2661, 48), (key2696, -160), (key2776, 64), (key2799, 528), (key2849, -480)]

def entry4_1 : Integer.Sparse Key := [(key970, 720), (key1084, -720)]

def entry4_2 : Integer.Sparse Key := [(key971, 192), (key979, 528), (key1085, -192), (key1093, -480), (key1164, -48), (key1228, -48), (key1245, 48)]

def entry4_3 : Integer.Sparse Key := [(key2372, -48), (key2385, 48), (key2400, 528), (key2432, 192), (key2466, -480), (key2475, -48), (key2498, -192)]

def entry4_4 : Integer.Sparse Key := [(key2353, 192), (key2359, 528), (key2448, -192), (key2454, -480), (key2515, -160), (key2566, 64), (key2578, 48)]

def entry5_0 : Integer.Sparse Key := [(key2378, 24), (key2390, 32), (key2394, 24), (key2406, 24), (key2437, 32), (key2443, 24), (key2480, 24), (key2503, 24), (key2524, 24), (key2571, 12), (key2576, 12), (key2580, 16), (key2587, -120), (key2593, -96), (key2598, 64), (key2600, 72), (key2766, -24), (key2772, -48), (key2843, -144), (key2880, -96), (key2887, 120), (key2889, 48), (key2910, 84), (key2929, 16), (key2931, -24), (key2966, -72), (key2968, -144), (key2989, -108), (key2995, 120), (key3002, 80)]

def entry5_1 : Integer.Sparse Key := [(key1026, 720), (key1104, -720)]

def entry5_2 : Integer.Sparse Key := [(key1001, -48), (key1015, 48), (key1028, 192), (key1036, 336), (key1071, 192), (key1106, -192), (key1114, -240), (key1123, -96), (key1150, -192), (key1232, -48), (key1235, 48)]

def entry5_3 : Integer.Sparse Key := [(key2610, 192), (key2626, -192), (key2665, 48), (key2700, -48), (key2780, -96), (key2789, 48), (key2803, 336), (key2824, 192), (key2853, -240), (key2855, -48), (key2865, -192)]

def entry5_5 : Integer.Sparse Key := [(key2608, 72), (key2614, 120), (key2624, -72), (key2630, -96), (key2638, -64), (key2657, 16), (key2659, 24), (key2663, 24), (key2669, 24), (key2698, -64), (key2704, -96), (key2724, -60), (key2752, 24), (key2757, 32), (key2778, 16), (key2792, 24), (key2801, 120), (key2807, 96), (key2827, 160), (key2851, -96), (key2858, -96), (key2868, -96), (key2919, 24), (key2922, 24), (key3007, 12), (key3009, 16), (key3011, 80), (key3016, 72), (key3021, -96), (key3022, -72), (key3025, -72)]

def entry6_0 : Integer.Sparse Key := [(key2455, -720), (key2516, 720)]

def entry6_1 : Integer.Sparse Key := [(key968, 720), (key1082, -720)]

def entry6_2 : Integer.Sparse Key := [(key973, 720), (key1087, -720)]

def entry6_3 : Integer.Sparse Key := [(key2368, 72), (key2396, 648), (key2462, -480), (key2581, -72), (key2760, 72), (key2837, -240)]

def entry6_4 : Integer.Sparse Key := [(key2355, 720), (key2450, -720)]

def entry6_5 : Integer.Sparse Key := [(key2764, 720), (key2841, -720)]

def entry6_6 : Integer.Sparse Key := [(key2351, 720), (key2446, -720)]

def entry7_0 : Integer.Sparse Key := [(key2587, 96), (key2593, 48), (key2598, -48), (key2600, -96), (key2766, -96), (key2772, -48), (key2887, -192), (key2889, -192), (key2910, -192), (key2929, 48), (key2931, 96), (key2966, 192), (key2968, 192), (key2989, 192)]

def entry7_1 : Integer.Sparse Key := [(key991, 720), (key1026, -720)]

def entry7_4 : Integer.Sparse Key := [(key2370, 144), (key2376, 288), (key2388, 144), (key2398, -144), (key2404, -288), (key2435, -144), (key2583, 48), (key2589, 96), (key2762, -48), (key2768, -96), (key2916, -96), (key2925, -48), (key3019, 96), (key3028, 48)]

def entry7_5 : Integer.Sparse Key := [(key2608, -48), (key2614, -96), (key2624, 48), (key2630, 48), (key2638, 48), (key2663, 48), (key2669, 96), (key2698, 144), (key2704, 144), (key2724, 144), (key2752, 96), (key2757, 48), (key2778, -48), (key2784, -48), (key2792, -48), (key2801, -144), (key2807, -144), (key2827, -176), (key2918, -48), (key2919, -48), (key2922, -48), (key3011, -64), (key3016, -48), (key3021, 48), (key3022, 48), (key3025, 48)]

def entry7_6 : Integer.Sparse Key := [(key2585, 720), (key2764, -720)]

def entry7_7 : Integer.Sparse Key := [(key2608, 96), (key2614, 192), (key2624, 96), (key2630, 96), (key2638, 128), (key2657, 64), (key2659, 48), (key2663, -96), (key2669, -192), (key2698, -192), (key2704, -192), (key2724, -192), (key2752, -192), (key2757, -96), (key2801, 96), (key2807, 96), (key2827, 128), (key3011, 64), (key3016, 48)]

def entry8_0 : Integer.Sparse Key := [(key1256, -96), (key1261, -96), (key1265, 96), (key1268, 96), (key1536, -48), (key1609, -144), (key1642, -96), (key1648, 144), (key1651, 48), (key1674, 96), (key1765, 48), (key1806, -48), (key1809, -144), (key1832, -96), (key1837, 144), (key1848, 96)]

def entry8_1 : Integer.Sparse Key := [(key377, 720), (key428, -720)]

def entry8_4 : Integer.Sparse Key := [(key1259, -48), (key1271, 48), (key1526, 192), (key1534, 336), (key1604, -192), (key1612, -240), (key1640, -48), (key1679, -96), (key1693, 48), (key1894, 192), (key1916, -192)]

def entry8_6 : Integer.Sparse Key := [(key1528, 720), (key1606, -720)]

def entry9_0 : Integer.Sparse Key := [(key2378, 120), (key2383, -48), (key2390, 80), (key2394, -72), (key2406, 120), (key2411, -48), (key2437, 80), (key2443, -72), (key2472, 96), (key2480, 120), (key2484, -96), (key2503, 120), (key2509, -96), (key2524, -72), (key2571, 12), (key2576, 12), (key2580, 16), (key2587, -24), (key2593, -48), (key2598, 16), (key2600, -24), (key2766, -24), (key2772, -48), (key2843, -48), (key2880, -48), (key2887, 24), (key2889, -48), (key2910, -12), (key2929, 16), (key2931, -24), (key2966, 24), (key2968, -48), (key2989, -12), (key2995, 24), (key3002, 32)]

def entry9_1 : Integer.Sparse Key := [(key1104, -720), (key1230, 720)]

def entry9_5 : Integer.Sparse Key := [(key2608, 24), (key2614, -24), (key2624, -24), (key2630, -96), (key2638, -64), (key2657, 112), (key2659, 72), (key2663, 24), (key2669, -24), (key2698, -16), (key2704, -96), (key2724, -60), (key2752, 120), (key2757, 80), (key2778, 16), (key2784, -48), (key2792, -24), (key2801, 24), (key2807, -48), (key2827, -16), (key2851, -48), (key2858, -96), (key2868, -96), (key2918, 96), (key2919, 120), (key2922, 120), (key3007, 12), (key3009, 16), (key3011, 16), (key3016, 24), (key3021, -48), (key3022, -24), (key3025, -24)]

def entry9_6 : Integer.Sparse Key := [(key2841, -720), (key2873, 720)]

def entry9_7 : Integer.Sparse Key := [(key2624, 48), (key2630, 48), (key2638, 48), (key2657, -96), (key2659, -48), (key2698, 48), (key2704, 48), (key2724, 48), (key2752, -96), (key2757, -48), (key2778, -48), (key2784, -48), (key2792, -48), (key2801, -48), (key2807, -48), (key2827, -48), (key2918, -144), (key2919, -144), (key2922, -144), (key3007, 96), (key3009, 48), (key3011, 96), (key3016, 48), (key3021, 144), (key3022, 144), (key3025, 144)]

def entry9_9 : Integer.Sparse Key := [(key2608, 72), (key2614, -72), (key2624, 120), (key2630, -96), (key2638, -64), (key2657, 16), (key2659, 24), (key2663, 72), (key2669, -72), (key2698, 160), (key2704, -96), (key2724, -60), (key2752, 24), (key2757, 32), (key2778, 80), (key2784, -96), (key2792, -72), (key2801, 120), (key2807, -96), (key2827, -64), (key2851, 96), (key2858, -96), (key2868, -96), (key2919, 24), (key2922, 24), (key3007, 12), (key3009, 16), (key3011, 16), (key3016, 24), (key3022, 24), (key3025, 24)]

def entry10_2 : Integer.Sparse Key := [(key20, -48), (key31, 48), (key45, 528), (key70, 192), (key102, -480), (key111, -48), (key133, -192)]

def entry10_3 : Integer.Sparse Key := [(key1287, 192), (key1307, -192), (key1382, 48), (key1415, -48), (key1537, -48), (key1564, 528), (key1613, -480)]

def entry10_4 : Integer.Sparse Key := [(key1250, -48), (key1269, 48), (key1525, 528), (key1603, -480), (key1677, -48), (key1892, 192), (key1914, -192)]

def entry10_5 : Integer.Sparse Key := [(key1289, 192), (key1309, -192), (key1384, 48), (key1417, -96), (key1471, 48), (key1539, -48), (key1566, 336), (key1615, -240), (key1680, -48), (key1902, 192), (key1917, -192)]

def entry10_6 : Integer.Sparse Key := [(key1523, 720), (key1601, -720)]

def entry11_0 : Integer.Sparse Key := [(key2361, 144), (key2364, -144), (key2456, 576), (key2520, -576), (key2531, 144), (key2561, -144)]

def entry11_1 : Integer.Sparse Key := [(key969, -720), (key1177, 720)]

def entry11_2 : Integer.Sparse Key := [(key972, -144), (key977, -576), (key1086, 144), (key1162, -144), (key1181, 576), (key1218, 144)]

def entry11_3 : Integer.Sparse Key := [(key2369, -144), (key2384, 144), (key2397, -576), (key2431, -144), (key2474, 576), (key2497, 144)]

def entry11_4 : Integer.Sparse Key := [(key2354, -144), (key2358, -576), (key2449, 144), (key2514, -144), (key2529, 576), (key2559, 144)]

def entry11_5 : Integer.Sparse Key := [(key2588, -144), (key2599, 144), (key2763, -144), (key2767, -432), (key2840, 144), (key2875, -144), (key2888, 432), (key2909, 144), (key2930, -144), (key2967, 144)]

def entry11_6 : Integer.Sparse Key := [(key2352, -720), (key2511, 720)]

def entry11_8 : Integer.Sparse Key := [(key1257, -144), (key1266, 144), (key1527, -144), (key1532, -432), (key1605, 144), (key1638, -144), (key1649, 432), (key1672, 144), (key1766, -144), (key1807, 144)]

def entry11_10 : Integer.Sparse Key := [(key1249, -144), (key1262, 144), (key1524, -576), (key1645, 576), (key1762, -144), (key1803, 144)]

def entry11_11 : Integer.Sparse Key := [(key2353, 288), (key2356, 432), (key2448, 432), (key2527, -864), (key2558, -288)]

def entry12_1 : Integer.Sparse Key := [(key970, -720), (key1226, 720)]

def entry12_2 : Integer.Sparse Key := [(key971, -144), (key979, -576), (key1085, 144), (key1164, -144), (key1228, 576), (key1245, 144)]

def entry12_3 : Integer.Sparse Key := [(key2372, -144), (key2385, 144), (key2400, -576), (key2432, -144), (key2475, 576), (key2498, 144)]

def entry12_4 : Integer.Sparse Key := [(key2353, -144), (key2359, -576), (key2448, 144), (key2566, 432), (key2578, 144)]

def entry12_6 : Integer.Sparse Key := [(key2355, -720), (key2512, 720)]

def entry12_7 : Integer.Sparse Key := [(key2370, -144), (key2376, -288), (key2388, -144), (key2398, 144), (key2404, 288), (key2435, 144), (key2604, -144), (key2916, -288), (key2925, -144), (key3005, 144), (key3019, 288), (key3028, 144)]

def entry12_8 : Integer.Sparse Key := [(key1259, -144), (key1271, 144), (key1526, -144), (key1534, -432), (key1604, 144), (key1640, -144), (key1679, 432), (key1693, 144), (key1894, -144), (key1916, 144)]

def entry12_10 : Integer.Sparse Key := [(key1250, -144), (key1269, 144), (key1525, -576), (key1677, 576), (key1892, -144), (key1914, 144)]

def entry12_11 : Integer.Sparse Key := [(key2354, 288), (key2358, 432), (key2449, 432), (key2514, -432), (key2529, -432), (key2559, -288)]

def entry12_12 : Integer.Sparse Key := [(key2353, 288), (key2359, 432), (key2448, 432), (key2566, -864), (key2578, -288)]

def entry13_0 : Integer.Sparse Key := [(key1999, 48), (key2003, -48), (key2268, -288), (key2272, -240), (key2294, -192), (key2323, 240), (key2324, 288), (key2336, 192)]

def entry13_1 : Integer.Sparse Key := [(key724, 720), (key942, -720)]

def entry13_2 : Integer.Sparse Key := [(key713, 192), (key715, 528), (key890, -192), (key892, -480), (key914, -48), (key959, -48), (key966, 48)]

def entry13_3 : Integer.Sparse Key := [(key2098, -48), (key2099, 48), (key2203, 528), (key2206, 192), (key2317, -480), (key2318, -48), (key2321, -192)]

def entry13_4 : Integer.Sparse Key := [(key1998, 192), (key2000, 528), (key2267, -192), (key2269, -480), (key2292, -48), (key2340, -48), (key2349, 48)]

def entry13_5 : Integer.Sparse Key := [(key2079, -48), (key2085, 48), (key2174, 192), (key2176, 336), (key2187, 192), (key2274, -192), (key2276, -240), (key2279, -96), (key2287, -192), (key2341, -48), (key2343, 48)]

def entry13_6 : Integer.Sparse Key := [(key2009, 720), (key2316, -720)]

def entry13_8 : Integer.Sparse Key := [(key738, -48), (key743, 48), (key817, 192), (key818, 336), (key825, 192), (key897, -192), (key898, -240), (key902, -96), (key908, -192), (key960, -48), (key962, 48)]

def entry13_10 : Integer.Sparse Key := [(key754, -48), (key755, 48), (key843, 528), (key844, 192), (key943, -480), (key944, -48), (key945, -192)]

def entry13_11 : Integer.Sparse Key := [(key2006, -144), (key2007, -576), (key2299, 144), (key2313, -144), (key2340, 576), (key2349, 144)]

def entry13_12 : Integer.Sparse Key := [(key1998, -144), (key2000, -576), (key2267, 144), (key2292, -144), (key2340, 576), (key2349, 144)]

def entry13_13 : Integer.Sparse Key := [(key776, 192), (key778, 528), (key801, -192), (key803, -480), (key811, -160), (key836, 64), (key839, 48)]

def entry14_0 : Integer.Sparse Key := [(key976, 144), (key984, -144), (key1090, 576), (key1169, 144), (key1183, -576), (key1220, -144)]

def entry14_1 : Integer.Sparse Key := [(key3, -720), (key147, 720)]

def entry14_2 : Integer.Sparse Key := [(key1, -144), (key7, -576), (key84, 144), (key193, 432), (key202, 144)]

def entry14_3 : Integer.Sparse Key := [(key995, -144), (key1011, 144), (key1030, -576), (key1067, -144), (key1119, 576), (key1146, 144)]

def entry14_4 : Integer.Sparse Key := [(key971, -144), (key979, -576), (key1085, 144), (key1164, 576), (key1228, -144), (key1245, 144)]

def entry14_5 : Integer.Sparse Key := [(key1001, -144), (key1015, 144), (key1028, -144), (key1036, -432), (key1071, -144), (key1106, 144), (key1123, 432), (key1150, 144), (key1232, -144), (key1235, 144)]

def entry14_6 : Integer.Sparse Key := [(key973, -720), (key1160, 720)]

def entry14_10 : Integer.Sparse Key := [(key20, -144), (key31, 144), (key45, -576), (key70, -144), (key111, 576), (key133, 144)]

def entry14_11 : Integer.Sparse Key := [(key972, 288), (key977, 432), (key1086, 432), (key1162, -432), (key1181, -432), (key1218, -288)]

def entry14_12 : Integer.Sparse Key := [(key971, 288), (key979, 432), (key1085, 432), (key1164, -432), (key1228, -432), (key1245, -288)]

def entry14_13 : Integer.Sparse Key := [(key713, -144), (key715, -576), (key890, 144), (key914, -144), (key959, 576), (key966, 144)]

def entry14_14 : Integer.Sparse Key := [(key1, 288), (key7, 432), (key84, 432), (key193, -864), (key202, -288)]

def entry15_0 : Integer.Sparse Key := [(key2361, 48), (key2364, -48), (key2456, -288), (key2459, -240), (key2517, 240), (key2520, 288), (key2531, -192), (key2561, 192)]

def entry15_1 : Integer.Sparse Key := [(key969, 720), (key1083, -720)]

def entry15_2 : Integer.Sparse Key := [(key972, 192), (key977, 528), (key1086, -192), (key1091, -480), (key1162, -48), (key1181, -48), (key1218, 48)]

def entry15_3 : Integer.Sparse Key := [(key2369, -48), (key2384, 48), (key2397, 528), (key2431, 192), (key2463, -480), (key2474, -48), (key2497, -192)]

def entry15_4 : Integer.Sparse Key := [(key2354, 192), (key2358, 528), (key2449, -192), (key2453, -480), (key2514, -48), (key2529, -48), (key2559, 48)]

def entry15_5 : Integer.Sparse Key := [(key2588, -48), (key2599, 48), (key2763, 192), (key2767, 336), (key2840, -192), (key2844, -240), (key2875, -48), (key2888, -96), (key2909, 48), (key2930, 192), (key2967, -192)]

def entry15_6 : Integer.Sparse Key := [(key2352, 720), (key2447, -720)]

def entry15_8 : Integer.Sparse Key := [(key1257, -48), (key1266, 48), (key1527, 192), (key1532, 336), (key1605, -192), (key1610, -240), (key1638, -48), (key1649, -96), (key1672, 48), (key1766, 192), (key1807, -192)]

def entry15_10 : Integer.Sparse Key := [(key1249, -48), (key1262, 48), (key1524, 528), (key1602, -480), (key1645, -48), (key1762, 192), (key1803, -192)]

def entry15_11 : Integer.Sparse Key := [(key2353, -144), (key2356, -576), (key2448, 144), (key2527, 432), (key2558, 144)]

def entry15_12 : Integer.Sparse Key := [(key2354, -144), (key2358, -576), (key2449, 144), (key2514, 576), (key2529, -144), (key2559, 144)]

def entry15_13 : Integer.Sparse Key := [(key2006, 192), (key2007, 528), (key2299, -192), (key2300, -480), (key2313, -48), (key2340, -48), (key2349, 48)]

def entry15_14 : Integer.Sparse Key := [(key972, -144), (key977, -576), (key1086, 144), (key1162, 576), (key1181, -144), (key1218, 144)]

def entry15_15 : Integer.Sparse Key := [(key2353, 192), (key2356, 528), (key2448, -192), (key2451, -480), (key2513, -160), (key2527, 64), (key2558, 48)]

def entry16_0 : Integer.Sparse Key := [(key2377, 144), (key2389, -144), (key2405, -144), (key2436, 144), (key2479, -576), (key2502, 576)]

def entry16_1 : Integer.Sparse Key := [(key989, 720), (key1024, -720)]

def entry16_2 : Integer.Sparse Key := [(key995, 576), (key1011, 144), (key1030, -576), (key1067, -144), (key1119, -144), (key1146, 144)]

def entry16_3 : Integer.Sparse Key := [(key2606, -144), (key2622, 144), (key2661, 144), (key2696, 576), (key2776, -144), (key2799, -576)]

def entry16_4 : Integer.Sparse Key := [(key2372, 576), (key2385, 144), (key2400, -576), (key2432, -144), (key2475, -144), (key2498, 144)]

def entry16_5 : Integer.Sparse Key := [(key2610, -144), (key2626, 144), (key2665, 144), (key2700, -144), (key2780, 432), (key2789, 144), (key2803, -432), (key2824, -144), (key2855, -144), (key2865, 144)]

def entry16_6 : Integer.Sparse Key := [(key2368, 576), (key2396, -576), (key2581, 144), (key2760, -144)]

def entry16_10 : Integer.Sparse Key := [(key1287, -144), (key1307, 144), (key1382, 144), (key1415, -144), (key1537, 576), (key1564, -576)]

def entry16_11 : Integer.Sparse Key := [(key2369, -432), (key2384, -288), (key2397, 432), (key2431, 288), (key2474, -432), (key2497, 432)]

def entry16_12 : Integer.Sparse Key := [(key2372, -432), (key2385, -288), (key2400, 432), (key2432, 288), (key2475, -432), (key2498, 432)]

def entry16_13 : Integer.Sparse Key := [(key2098, 576), (key2099, 144), (key2203, -576), (key2206, -144), (key2318, -144), (key2321, 144)]

def entry16_14 : Integer.Sparse Key := [(key995, -432), (key1011, -288), (key1030, 432), (key1067, 288), (key1119, -432), (key1146, 432)]

def entry16_15 : Integer.Sparse Key := [(key2369, 576), (key2384, 144), (key2397, -576), (key2431, -144), (key2474, -144), (key2497, 144)]

def entry16_16 : Integer.Sparse Key := [(key2606, 288), (key2622, 432), (key2661, -288), (key2696, -864), (key2799, 432)]

def entry17_0 : Integer.Sparse Key := [(key2379, 24), (key2393, 64), (key2407, 24), (key2441, 64), (key2544, 32), (key2555, 32), (key2565, 48), (key2592, -24), (key2595, -192), (key2602, 128), (key2771, 24), (key2774, -96), (key2848, -48), (key2882, -192), (key2891, 96), (key2912, 160), (key2933, 32), (key2934, -48), (key2970, -96), (key2991, -32), (key2993, -192), (key2996, 48), (key3003, 144)]

def entry17_1 : Integer.Sparse Key := [(key1031, 720), (key1109, -720)]

def entry17_2 : Integer.Sparse Key := [(key1006, -48), (key1019, 48), (key1033, 384), (key1041, 144), (key1076, 192), (key1111, -384), (key1127, -144), (key1155, -192), (key1193, -96), (key1199, 96)]

def entry17_3 : Integer.Sparse Key := [(key2615, 192), (key2631, -192), (key2670, 48), (key2705, -48), (key2785, -144), (key2793, 96), (key2808, 144), (key2828, 384), (key2859, -96), (key2869, -384)]

def entry17_4 : Integer.Sparse Key := [(key2374, 48), (key2391, 36), (key2402, 336), (key2408, 144), (key2439, 180), (key2468, -288), (key2481, -144), (key2505, -144), (key2535, 24), (key2542, 48), (key2553, 48), (key2591, -48), (key2596, -48), (key2605, 12), (key2770, 48), (key2847, -96), (key2878, -24), (key2884, -96), (key2926, 48), (key3006, 12), (key3020, -48), (key3029, -48)]

def entry17_5 : Integer.Sparse Key := [(key2612, 72), (key2616, 72), (key2618, 32), (key2621, 16), (key2628, -96), (key2632, -48), (key2640, -16), (key2641, -48), (key2644, -48), (key2646, 16), (key2653, 32), (key2660, 16), (key2667, 24), (key2671, 24), (key2702, -96), (key2706, -48), (key2726, -12), (key2728, -48), (key2732, -48), (key2735, 24), (key2747, 36), (key2758, 24), (key2794, 24), (key2805, 48), (key2809, 48), (key2829, 96), (key2831, 36), (key2835, 48), (key2860, -48), (key2870, -48), (key2885, -48), (key2927, 24), (key2936, 12), (key2943, 24), (key2948, 48), (key2950, 48), (key2960, 96), (key2972, -96), (key2976, -96), (key2983, -96), (key2998, 24), (key3000, 24), (key3010, 12), (key3012, 12), (key3017, 48), (key3023, -48), (key3026, -48), (key3030, -24)]

def entry17_6 : Integer.Sparse Key := [(key2769, 720), (key2846, -720)]

def entry17_7 : Integer.Sparse Key := [(key2612, -48), (key2616, -48), (key2618, -32), (key2621, -16), (key2628, 96), (key2641, 48), (key2667, 96), (key2673, 48), (key2702, 192), (key2728, 96), (key2735, 96), (key2737, 96), (key2747, 96), (key2782, -96), (key2795, -48), (key2805, -144), (key2809, -48), (key2829, -64), (key2831, -84), (key2835, -48), (key2893, -96), (key2897, -96), (key2904, -96), (key2948, -32), (key2950, -48), (key2960, -64), (key2972, 96), (key2976, 96), (key2983, 96), (key3012, -12), (key3017, -32)]

def entry17_9 : Integer.Sparse Key := [(key2612, 24), (key2616, 24), (key2621, -48), (key2632, -48), (key2640, -16), (key2644, -144), (key2646, 16), (key2653, 32), (key2658, 48), (key2660, 112), (key2667, 24), (key2671, 24), (key2676, -48), (key2706, -48), (key2726, -12), (key2732, -144), (key2735, 24), (key2747, 36), (key2753, 48), (key2758, 120), (key2794, 24), (key2798, -96), (key2829, 32), (key2835, -96), (key2860, -48), (key2870, -48), (key2885, -144), (key2920, 96), (key2923, 96), (key2927, 120), (key2936, 12), (key2943, 24), (key2948, 16), (key2960, 32), (key2998, 24), (key3000, 24), (key3010, 12), (key3017, 16), (key3023, -48), (key3026, -48), (key3030, -24)]

def entry17_10 : Integer.Sparse Key := [(key1294, 192), (key1314, -192), (key1389, 48), (key1422, -144), (key1453, 96), (key1544, -48), (key1571, 144), (key1653, -96), (key1786, 384), (key1811, -384)]

def entry17_11 : Integer.Sparse Key := [(key2594, -144), (key2601, 144), (key2770, -288), (key2773, -288), (key2847, 288), (key2881, -288), (key2890, 288), (key2911, 288), (key2932, -144), (key2969, 144)]

def entry17_12 : Integer.Sparse Key := [(key2402, -288), (key2408, -144), (key2439, -144), (key2468, 288), (key2481, 144), (key2505, 144), (key2596, -144), (key2605, 144), (key2775, -144), (key2884, -288), (key2917, 144), (key2926, 288)]

def entry17_13 : Integer.Sparse Key := [(key2082, -48), (key2087, 48), (key2175, 384), (key2179, 144), (key2189, 192), (key2275, -384), (key2281, -144), (key2289, -192), (key2328, -96), (key2330, 96)]

def entry17_14 : Integer.Sparse Key := [(key1006, -144), (key1019, 144), (key1033, -288), (key1041, -288), (key1076, -144), (key1111, 288), (key1127, 288), (key1155, 144), (key1193, -288), (key1199, 288)]

def entry17_15 : Integer.Sparse Key := [(key2594, -48), (key2601, 48), (key2770, 384), (key2773, 144), (key2847, -384), (key2881, -96), (key2890, -144), (key2911, 96), (key2932, 192), (key2969, -192)]

def entry17_16 : Integer.Sparse Key := [(key2615, -144), (key2631, 144), (key2670, 144), (key2705, -144), (key2785, 288), (key2793, 288), (key2808, -288), (key2828, -288), (key2859, -288), (key2869, 288)]

def entry17_17 : Integer.Sparse Key := [(key2617, 96), (key2620, 96), (key2633, -96), (key2643, -192), (key2655, 96), (key2672, 48), (key2707, -96), (key2730, -192), (key2749, 128), (key2810, 48), (key2833, 128), (key2945, 64), (key2952, 64), (key2962, 192), (key2964, 96), (key2978, -192), (key2985, -192), (key2994, -192), (key3004, 96)]

def entry18_1 : Integer.Sparse Key := [(key91, -720), (key152, 720)]

def entry18_2 : Integer.Sparse Key := [(key9, 48), (key11, -64), (key14, 16), (key88, -336), (key92, 48), (key94, -240), (key153, 64), (key156, -204), (key161, 48), (key165, 176), (key167, 240), (key187, 160), (key194, 12), (key203, 32)]

def entry18_3 : Integer.Sparse Key := [(key1002, -192), (key1016, 192), (key1037, -48), (key1072, 48), (key1115, -240), (key1124, 288), (key1151, -288), (key1167, 240)]

def entry18_4 : Integer.Sparse Key := [(key981, 48), (key987, -48), (key1095, -288), (key1101, -240), (key1166, 240), (key1173, 288), (key1229, -192), (key1246, 192)]

def entry18_6 : Integer.Sparse Key := [(key1094, -720), (key1165, 720)]

def entry18_10 : Integer.Sparse Key := [(key24, -192), (key36, 192), (key49, -48), (key75, 48), (key106, -240), (key116, 288), (key138, -288), (key154, 240)]

def entry18_11 : Integer.Sparse Key := [(key981, 144), (key985, -144), (key1095, 576), (key1170, -576), (key1184, 144), (key1221, -144)]

def entry18_12 : Integer.Sparse Key := [(key981, 144), (key987, -144), (key1095, 576), (key1173, -576), (key1229, 144), (key1246, -144)]

def entry18_13 : Integer.Sparse Key := [(key714, 48), (key718, -48), (key891, -288), (key895, -240), (key916, -192), (key947, 240), (key948, 288), (key955, 192)]

def entry18_14 : Integer.Sparse Key := [(key9, 144), (key14, -144), (key88, 288), (key92, 288), (key94, 144), (key97, -144), (key153, 144), (key156, 144), (key161, -288), (key165, -144), (key167, -288), (key187, -144)]

def entry18_15 : Integer.Sparse Key := [(key981, 48), (key985, -48), (key1095, -288), (key1099, -240), (key1166, 240), (key1170, 288), (key1184, -192), (key1221, 192)]

def entry18_16 : Integer.Sparse Key := [(key1002, 144), (key1016, -144), (key1037, -144), (key1072, 144), (key1124, -576), (key1151, 576)]

def entry19_0 : Integer.Sparse Key := [(key2420, -240), (key2438, 240), (key2495, -240), (key2504, 240)]

def entry19_1 : Integer.Sparse Key := [(key1045, 720), (key1131, -720)]

def entry19_2 : Integer.Sparse Key := [(key1050, 240), (key1058, 480), (key1136, -240), (key1138, -480)]

def entry19_3 : Integer.Sparse Key := [(key2677, 288), (key2708, -360), (key2811, 144), (key2861, -144), (key3045, 192), (key3059, -120), (key3094, 96), (key3122, -96)]

def entry19_4 : Integer.Sparse Key := [(key2416, 240), (key2423, 480), (key2489, -240), (key2491, -480)]

def entry19_5 : Integer.Sparse Key := [(key2681, 240), (key2688, 240), (key2712, -240), (key2714, -240), (key2817, 240), (key2863, -240)]

def entry19_6 : Integer.Sparse Key := [(key2412, 720), (key2485, -540), (key3118, -180)]

def entry19_7 : Integer.Sparse Key := [(key2712, 240), (key2714, 480), (key2815, -240), (key2817, -480)]

def entry19_8 : Integer.Sparse Key := [(key1407, 240), (key1411, 240), (key1435, -240), (key1436, -240), (key1585, 240), (key1628, -240)]

def entry19_9 : Integer.Sparse Key := [(key2681, -240), (key2688, 240), (key2712, -240), (key2714, 240), (key2815, -240), (key2817, 240)]

def entry19_10 : Integer.Sparse Key := [(key1402, 480), (key1430, -480), (key1579, 240), (key1627, -240)]

def entry19_11 : Integer.Sparse Key := [(key2413, -720), (key2490, 720)]

def entry19_12 : Integer.Sparse Key := [(key2416, -720), (key2491, 720)]

def entry19_13 : Integer.Sparse Key := [(key2204, 240), (key2205, 480), (key2319, -240), (key2320, -480)]

def entry19_14 : Integer.Sparse Key := [(key1050, -720), (key1138, 720)]

def entry19_15 : Integer.Sparse Key := [(key2413, 240), (key2422, 480), (key2486, -240), (key2490, -480)]

def entry19_16 : Integer.Sparse Key := [(key2677, 144), (key2708, 720), (key2811, -528), (key3045, -144), (key3094, -192)]

def entry19_17 : Integer.Sparse Key := [(key2692, 480), (key2718, -480), (key2830, 240), (key2871, -240)]

def entry19_18 : Integer.Sparse Key := [(key1055, -240), (key1074, 240), (key1143, -240), (key1153, 240)]

def entry19_19 : Integer.Sparse Key := [(key3079, 240), (key3084, 240), (key3099, -480)]

def entry20_0 : Integer.Sparse Key := [(key1851, 720), (key1855, -720)]

def entry20_1 : Integer.Sparse Key := [(key685, -720), (key692, 720)]

def entry20_2 : Integer.Sparse Key := [(key619, -720), (key645, 720)]

def entry20_3 : Integer.Sparse Key := [(key1958, -720), (key1960, 720)]

def entry20_4 : Integer.Sparse Key := [(key1852, -720), (key1884, 720)]

def entry20_5 : Integer.Sparse Key := [(key1861, -720), (key1867, 720)]

def entry20_6 : Integer.Sparse Key := [(key1957, -720), (key1969, 720)]

def entry20_7 : Integer.Sparse Key := [(key1867, -720), (key1877, 720)]

def entry20_8 : Integer.Sparse Key := [(key627, -720), (key629, 720)]

def entry20_9 : Integer.Sparse Key := [(key1859, 720), (key1861, -720)]

def entry20_10 : Integer.Sparse Key := [(key686, -720), (key687, 720)]

def entry20_11 : Integer.Sparse Key := [(key1932, 720), (key1953, -720)]

def entry20_12 : Integer.Sparse Key := [(key1850, 720), (key1884, -720)]

def entry20_13 : Integer.Sparse Key := [(key362, -720), (key366, 720)]

def entry20_14 : Integer.Sparse Key := [(key617, 720), (key645, -720)]

def entry20_15 : Integer.Sparse Key := [(key1933, -720), (key1953, 720)]

def entry20_16 : Integer.Sparse Key := [(key1960, -720), (key1966, 720)]

def entry20_17 : Integer.Sparse Key := [(key1864, -720), (key1869, 720)]

def entry20_18 : Integer.Sparse Key := [(key618, 720), (key622, -720)]

def entry20_19 : Integer.Sparse Key := [(key1962, -720), (key1964, 720)]

def entry20_20 : Integer.Sparse Key := [(key288, 720), (key289, -720)]

def entry21_0 : Integer.Sparse Key := [(key2378, 96), (key2381, -96), (key2390, 96), (key2392, -96), (key2406, 96), (key2409, -96), (key2437, 96), (key2440, -96), (key2472, 48), (key2480, 144), (key2482, -144), (key2503, 144), (key2506, -144), (key2522, -48), (key2538, -48), (key2563, 48)]

def entry21_1 : Integer.Sparse Key := [(key1103, -720), (key1187, 720)]

def entry21_2 : Integer.Sparse Key := [(key994, 48), (key999, -48), (key1029, 48), (key1034, -48), (key1107, -96), (key1112, -240), (key1121, -192), (key1148, -192), (key1191, 336), (key1197, 192), (key1210, 192)]

def entry21_3 : Integer.Sparse Key := [(key2623, -192), (key2634, 192), (key2697, -48), (key2720, 48), (key2777, -192), (key2788, 192), (key2800, -48), (key2823, 48), (key2850, -240), (key2854, 336), (key2864, -96)]

def entry21_4 : Integer.Sparse Key := [(key2371, 48), (key2375, -48), (key2399, 48), (key2403, -48), (key2465, -96), (key2469, -240), (key2477, -192), (key2500, -192), (key2536, 336), (key2541, 192), (key2552, 192)]

def entry21_5 : Integer.Sparse Key := [(key2609, 24), (key2613, -24), (key2625, -24), (key2629, -96), (key2637, -72), (key2647, 120), (key2652, 72), (key2664, 24), (key2668, -24), (key2699, -24), (key2703, -96), (key2723, -72), (key2736, 120), (key2746, 72), (key2779, 24), (key2783, -48), (key2791, -24), (key2802, 24), (key2806, -48), (key2826, -24), (key2852, -48), (key2857, -96), (key2867, -96), (key2894, 96), (key2896, 120), (key2903, 120), (key2937, 24), (key2942, 24), (key2949, 24), (key2959, 24), (key2973, -48), (key2975, -24), (key2982, -24)]

def entry21_6 : Integer.Sparse Key := [(key2838, -720), (key2872, 720)]

def entry21_7 : Integer.Sparse Key := [(key2625, 48), (key2629, 48), (key2637, 48), (key2647, -96), (key2652, -48), (key2699, 48), (key2703, 48), (key2723, 48), (key2736, -96), (key2746, -48), (key2779, -48), (key2783, -48), (key2791, -48), (key2802, -48), (key2806, -48), (key2826, -48), (key2894, -144), (key2896, -144), (key2903, -144), (key2937, 96), (key2942, 48), (key2949, 96), (key2959, 48), (key2973, 144), (key2975, 144), (key2982, 144)]

def entry21_8 : Integer.Sparse Key := [(key1292, 24), (key1297, -24), (key1312, -24), (key1317, -96), (key1325, -72), (key1338, 120), (key1344, 72), (key1387, 24), (key1392, -24), (key1420, -24), (key1425, -96), (key1443, -72), (key1456, 120), (key1465, 72), (key1542, 24), (key1547, -48), (key1555, -24), (key1569, 24), (key1574, -48), (key1592, -24), (key1618, -48), (key1623, -96), (key1632, -96), (key1656, 96), (key1658, 120), (key1666, 120), (key1773, 24), (key1779, 24), (key1789, 24), (key1797, 24), (key1814, -48), (key1816, -24), (key1824, -24)]

def entry21_9 : Integer.Sparse Key := [(key2609, 72), (key2613, -72), (key2625, 120), (key2629, -96), (key2637, -24), (key2647, -24), (key2652, 24), (key2664, 72), (key2668, -72), (key2699, 120), (key2703, -96), (key2723, -24), (key2736, -24), (key2746, 24), (key2779, 120), (key2783, -96), (key2791, -24), (key2802, 120), (key2806, -96), (key2826, -24), (key2852, 96), (key2857, -48), (key2867, -48), (key2894, -48), (key2896, 24), (key2903, 24), (key2937, -24), (key2942, 24), (key2949, -24), (key2959, 24), (key2973, -48), (key2975, 24), (key2982, 24)]

def entry21_10 : Integer.Sparse Key := [(key1308, -192), (key1334, 192), (key1416, -192), (key1452, 192), (key1538, -48), (key1565, -48), (key1614, -240), (key1652, 336), (key1769, 48), (key1785, 48), (key1810, -96)]

def entry21_12 : Integer.Sparse Key := [(key2371, 144), (key2375, -144), (key2399, 144), (key2403, -144), (key2465, 432), (key2477, 144), (key2500, 144), (key2536, -432), (key2541, -144), (key2552, -144)]

def entry21_13 : Integer.Sparse Key := [(key2091, 48), (key2092, -48), (key2193, 48), (key2194, -48), (key2302, -96), (key2303, -240), (key2305, -192), (key2310, -192), (key2341, 336), (key2343, 192), (key2347, 192)]

def entry21_14 : Integer.Sparse Key := [(key994, 144), (key999, -144), (key1029, 144), (key1034, -144), (key1107, 432), (key1121, 144), (key1148, 144), (key1191, -432), (key1197, -144), (key1210, -144)]

def entry21_16 : Integer.Sparse Key := [(key2623, 144), (key2634, -144), (key2697, -144), (key2720, 144), (key2777, 144), (key2788, -144), (key2800, -144), (key2823, 144), (key2854, -432), (key2864, 432)]

def entry21_17 : Integer.Sparse Key := [(key2616, 48), (key2619, -48), (key2632, -48), (key2642, -144), (key2649, 48), (key2654, 144), (key2671, 48), (key2674, -48), (key2706, -48), (key2729, -144), (key2738, 48), (key2748, 144), (key2794, 48), (key2796, -96), (key2829, 48), (key2832, -96), (key2860, -48), (key2870, -48), (key2883, -144), (key2898, 96), (key2905, 96), (key2913, 144), (key2944, 48), (key2961, 48), (key2977, -48), (key2984, -48)]

def entry21_19 : Integer.Sparse Key := [(key2678, -240), (key2687, 240), (key2709, -240), (key2713, 240), (key2812, -240), (key2816, 240)]

def entry21_20 : Integer.Sparse Key := [(key1936, 720), (key1937, -720)]

def entry21_21 : Integer.Sparse Key := [(key2608, 72), (key2611, -72), (key2624, 120), (key2627, -96), (key2636, -64), (key2645, 16), (key2651, 24), (key2663, 72), (key2666, -72), (key2698, 160), (key2701, -96), (key2722, -60), (key2734, 24), (key2745, 32), (key2778, 80), (key2781, -96), (key2790, -72), (key2801, 120), (key2804, -96), (key2825, -64), (key2851, 96), (key2856, -96), (key2866, -96), (key2895, 24), (key2902, 24), (key2935, 12), (key2941, 16), (key2947, 16), (key2958, 24), (key2974, 24), (key2981, 24)]

def entry22_0 : Integer.Sparse Key := [(key2378, -96), (key2381, -96), (key2390, 96), (key2392, 96), (key2409, -48), (key2437, 48), (key2472, -144), (key2480, 144), (key2482, 48), (key2503, -48), (key2506, -144), (key2522, 144), (key2538, -96), (key2543, 96), (key2554, -96), (key2563, 96)]

def entry22_1 : Integer.Sparse Key := [(key1025, 720), (key1103, -720)]

def entry22_2 : Integer.Sparse Key := [(key999, -48), (key1013, 48), (key1029, 192), (key1034, 336), (key1069, 192), (key1107, -192), (key1112, -240), (key1121, -96), (key1148, -192), (key1191, -48), (key1197, 48)]

def entry22_3 : Integer.Sparse Key := [(key2607, 192), (key2623, -192), (key2662, 48), (key2697, -48), (key2777, -96), (key2788, 48), (key2800, 336), (key2823, 192), (key2850, -240), (key2854, -48), (key2864, -192)]

def entry22_4 : Integer.Sparse Key := [(key2375, -48), (key2387, 48), (key2399, 192), (key2403, 336), (key2434, 192), (key2465, -192), (key2469, -240), (key2477, -96), (key2500, -192), (key2536, -48), (key2541, 48)]

def entry22_5 : Integer.Sparse Key := [(key2609, 72), (key2613, 120), (key2625, -72), (key2629, -96), (key2637, -24), (key2647, -24), (key2652, 24), (key2664, 24), (key2668, 24), (key2699, -24), (key2703, -48), (key2723, -24), (key2736, 24), (key2746, 24), (key2779, -24), (key2783, -48), (key2791, 24), (key2802, 120), (key2806, 96), (key2826, 120), (key2852, -96), (key2857, -48), (key2867, -96), (key2894, -48), (key2896, 24), (key2903, -24), (key2937, -24), (key2942, 24), (key2949, 120), (key2959, 72), (key2973, -96), (key2975, -24), (key2982, -72)]

def entry22_6 : Integer.Sparse Key := [(key2761, 720), (key2838, -720)]

def entry22_7 : Integer.Sparse Key := [(key2609, -48), (key2613, -96), (key2625, 48), (key2629, 48), (key2637, 48), (key2664, 48), (key2668, 96), (key2699, 144), (key2703, 144), (key2723, 144), (key2736, 96), (key2746, 48), (key2779, -48), (key2783, -48), (key2791, -48), (key2802, -144), (key2806, -144), (key2826, -144), (key2894, -48), (key2896, -48), (key2903, -48), (key2949, -96), (key2959, -48), (key2973, 48), (key2975, 48), (key2982, 48)]

def entry22_8 : Integer.Sparse Key := [(key1292, 72), (key1297, 120), (key1312, -72), (key1317, -96), (key1325, -24), (key1338, -24), (key1344, 24), (key1387, 24), (key1392, 24), (key1420, -24), (key1425, -48), (key1443, -24), (key1456, 24), (key1465, 24), (key1542, -24), (key1547, -48), (key1555, 24), (key1569, 120), (key1574, 96), (key1592, 120), (key1618, -96), (key1623, -48), (key1632, -96), (key1656, -48), (key1658, 24), (key1666, -24), (key1773, -24), (key1779, 24), (key1789, 120), (key1797, 72), (key1814, -96), (key1816, -24), (key1824, -72)]

def entry22_9 : Integer.Sparse Key := [(key2609, 24), (key2613, -24), (key2625, -24), (key2629, -96), (key2637, 120), (key2647, -72), (key2652, 72), (key2664, 24), (key2668, -24), (key2699, 24), (key2703, -48), (key2723, 24), (key2736, -24), (key2746, 24), (key2779, -24), (key2783, -96), (key2791, 120), (key2802, 24), (key2806, -48), (key2826, 24), (key2852, -48), (key2857, 96), (key2867, -48), (key2894, -96), (key2896, 120), (key2903, -24), (key2937, -72), (key2942, 72), (key2949, -24), (key2959, 24), (key2973, -96), (key2975, 120), (key2982, -24)]

def entry22_10 : Integer.Sparse Key := [(key1288, 192), (key1308, -192), (key1383, 48), (key1416, -96), (key1452, 48), (key1538, -48), (key1565, 336), (key1614, -240), (key1652, -48), (key1785, 192), (key1810, -192)]

def entry22_12 : Integer.Sparse Key := [(key2375, -144), (key2387, 144), (key2399, -144), (key2403, -432), (key2434, -144), (key2465, 144), (key2477, 432), (key2500, 144), (key2536, -144), (key2541, 144)]

def entry22_13 : Integer.Sparse Key := [(key2092, -48), (key2095, 48), (key2193, 192), (key2194, 336), (key2200, 192), (key2302, -192), (key2303, -240), (key2305, -96), (key2310, -192), (key2341, -48), (key2343, 48)]

def entry22_14 : Integer.Sparse Key := [(key999, -144), (key1013, 144), (key1029, -144), (key1034, -432), (key1069, -144), (key1107, 144), (key1121, 432), (key1148, 144), (key1191, -144), (key1197, 144)]

def entry22_16 : Integer.Sparse Key := [(key2607, -144), (key2623, 144), (key2662, 144), (key2697, -144), (key2777, 432), (key2788, 144), (key2800, -432), (key2823, -144), (key2854, -144), (key2864, 144)]

def entry22_17 : Integer.Sparse Key := [(key2616, 144), (key2619, 48), (key2632, -144), (key2642, -48), (key2649, -48), (key2654, 48), (key2671, 48), (key2706, -48), (key2729, -48), (key2748, 48), (key2786, -96), (key2794, 48), (key2809, 96), (key2829, 144), (key2832, 96), (key2860, -48), (key2870, -144), (key2883, -48), (key2905, -96), (key2913, 48), (key2939, -48), (key2944, 48), (key2951, 48), (key2961, 144), (key2977, -48), (key2984, -144)]

def entry22_19 : Integer.Sparse Key := [(key2678, 240), (key2687, 240), (key2709, -240), (key2713, -240), (key2816, 240), (key2862, -240)]

def entry22_20 : Integer.Sparse Key := [(key1937, -720), (key1940, 720)]

def entry22_21 : Integer.Sparse Key := [(key2608, 24), (key2611, -24), (key2624, -24), (key2627, -96), (key2636, -64), (key2645, 112), (key2651, 72), (key2663, 24), (key2666, -24), (key2698, -16), (key2701, -96), (key2722, -60), (key2734, 120), (key2745, 80), (key2778, 16), (key2781, -48), (key2790, -24), (key2801, 24), (key2804, -48), (key2825, -16), (key2851, -48), (key2856, -96), (key2866, -96), (key2892, 96), (key2895, 120), (key2902, 120), (key2935, 12), (key2941, 16), (key2947, 16), (key2958, 24), (key2971, -48), (key2974, -24), (key2981, -24)]

def entry22_22 : Integer.Sparse Key := [(key2608, 72), (key2611, 120), (key2624, -72), (key2627, -96), (key2636, -64), (key2645, 16), (key2651, 24), (key2663, 24), (key2666, 24), (key2698, -64), (key2701, -96), (key2722, -60), (key2734, 24), (key2745, 32), (key2778, 16), (key2790, 24), (key2801, 120), (key2804, 96), (key2825, 160), (key2851, -96), (key2856, -96), (key2866, -96), (key2895, 24), (key2902, 24), (key2935, 12), (key2941, 16), (key2947, 80), (key2958, 72), (key2971, -96), (key2974, -72), (key2981, -72)]

def entry23_0 : Integer.Sparse Key := [(key2362, 48), (key2367, -48), (key2457, -48), (key2460, -288), (key2521, -160), (key2525, -192), (key2532, 256), (key2533, 48), (key2562, 192), (key2564, 192)]

def entry23_1 : Integer.Sparse Key := [(key974, 720), (key1088, -720)]

def entry23_2 : Integer.Sparse Key := [(key976, 384), (key984, 336), (key1090, -384), (key1098, -240), (key1169, -96), (key1183, -96), (key1220, 96)]

def entry23_3 : Integer.Sparse Key := [(key2377, -96), (key2389, 96), (key2405, 336), (key2436, 384), (key2471, -240), (key2479, -96), (key2502, -384)]

def entry23_5 : Integer.Sparse Key := [(key2378, 24), (key2390, 32), (key2394, 24), (key2406, 216), (key2411, 96), (key2437, 128), (key2443, 216), (key2472, -96), (key2480, -72), (key2484, -96), (key2503, -72), (key2509, -96), (key2524, -72), (key2571, 12), (key2576, 12), (key2580, 16), (key2587, -72), (key2593, -48), (key2598, 16), (key2600, 24), (key2766, 24), (key2843, -96), (key2880, -48), (key2887, 24), (key2910, 36), (key2929, 16), (key2931, 24), (key2966, -72), (key2968, -96), (key2989, -60), (key2995, 24), (key3002, 32)]

def entry23_6 : Integer.Sparse Key := [(key2360, 720), (key2455, -720)]

def entry23_7 : Integer.Sparse Key := [(key2378, 192), (key2383, 96), (key2390, 96), (key2394, 192), (key2406, -192), (key2411, -96), (key2437, -96), (key2443, -192), (key2587, 96), (key2593, 48), (key2766, -96), (key2772, -48), (key2887, -96), (key2889, -96), (key2910, -96), (key2966, 96), (key2968, 96), (key2989, 96)]

def entry23_8 : Integer.Sparse Key := [(key1256, -48), (key1261, -48), (key1265, 48), (key1268, 48), (key1531, 240), (key1536, 96), (key1609, -192), (key1642, -48), (key1648, -48), (key1651, -96), (key1674, 48), (key1765, 144), (key1768, 240), (key1806, -144), (key1809, -192), (key1832, -48), (key1837, -48), (key1848, 48)]

def entry23_9 : Integer.Sparse Key := [(key2378, 24), (key2383, -48), (key2390, 32), (key2394, -72), (key2406, 24), (key2411, -48), (key2437, 32), (key2443, -72), (key2472, -96), (key2480, -72), (key2484, -192), (key2503, -72), (key2509, -192), (key2524, -168), (key2569, 96), (key2571, 204), (key2576, 204), (key2580, 112), (key2587, 24), (key2598, 16), (key2600, 24), (key2766, 24), (key2887, 24), (key2910, 36), (key2929, 16), (key2931, 24), (key2966, 24), (key2989, 36), (key2995, 24), (key3002, 32)]

def entry23_11 : Integer.Sparse Key := [(key2361, -288), (key2364, -432), (key2456, 288), (key2520, -288), (key2531, 432), (key2561, 288)]

def entry23_13 : Integer.Sparse Key := [(key1999, 384), (key2003, 336), (key2268, -384), (key2272, -240), (key2294, -96), (key2324, -96), (key2336, 96)]

def entry23_14 : Integer.Sparse Key := [(key976, -288), (key984, -432), (key1090, 288), (key1169, 432), (key1183, -288), (key1220, 288)]

def entry23_15 : Integer.Sparse Key := [(key2361, 384), (key2364, 336), (key2456, -384), (key2459, -240), (key2520, -96), (key2531, -96), (key2561, 96)]

def entry23_16 : Integer.Sparse Key := [(key2377, 432), (key2389, 288), (key2405, -432), (key2436, -288), (key2479, -288), (key2502, 288)]

def entry23_17 : Integer.Sparse Key := [(key2379, 24), (key2393, 64), (key2407, 120), (key2410, 192), (key2441, 256), (key2445, 96), (key2473, -96), (key2483, -192), (key2507, -192), (key2526, -96), (key2544, 32), (key2555, 32), (key2565, 48), (key2592, -24), (key2595, -96), (key2602, 32), (key2771, 24), (key2848, -48), (key2882, -96), (key2912, 64), (key2933, 32), (key2970, -96), (key2991, -32), (key2993, -96), (key3003, 48)]

def entry23_19 : Integer.Sparse Key := [(key2427, 480), (key2438, 240), (key2495, -480), (key2504, -240)]

def entry23_20 : Integer.Sparse Key := [(key1855, -720), (key1886, 720)]

def entry23_21 : Integer.Sparse Key := [(key2378, 48), (key2381, -48), (key2390, 48), (key2392, -48), (key2406, 48), (key2409, -48), (key2437, 48), (key2440, -48), (key2472, -96), (key2480, -48), (key2482, -192), (key2503, -48), (key2506, -192), (key2522, -144), (key2538, 96), (key2543, 240), (key2554, 240), (key2563, 144)]

def entry23_22 : Integer.Sparse Key := [(key2378, -48), (key2381, -48), (key2390, 48), (key2392, 48), (key2406, 240), (key2409, 96), (key2437, 144), (key2440, 240), (key2472, -192), (key2480, -48), (key2482, -96), (key2503, -144), (key2506, -192), (key2522, -48), (key2538, -48), (key2543, 48), (key2554, -48), (key2563, 48)]

def entry24_0 : Integer.Sparse Key := [(key1700, -720), (key1851, 720)]

def entry24_1 : Integer.Sparse Key := [(key219, 720), (key491, -720)]

def entry24_2 : Integer.Sparse Key := [(key30, 720), (key110, -720)]

def entry24_3 : Integer.Sparse Key := [(key1483, 720), (key1709, -720)]

def entry24_4 : Integer.Sparse Key := [(key1274, 720), (key1697, -720)]

def entry24_5 : Integer.Sparse Key := [(key1485, 720), (key1711, -720)]

def entry24_6 : Integer.Sparse Key := [(key1272, 720), (key1695, -720)]

def entry24_7 : Integer.Sparse Key := [(key1359, 720), (key1485, -720)]

def entry24_8 : Integer.Sparse Key := [(key395, 720), (key440, -720)]

def entry24_9 : Integer.Sparse Key := [(key1711, -720), (key1936, 720)]

def entry24_10 : Integer.Sparse Key := [(key348, 720), (key505, -720)]

def entry24_11 : Integer.Sparse Key := [(key1273, -720), (key1850, 720)]

def entry24_12 : Integer.Sparse Key := [(key1274, -720), (key1932, 720)]

def entry24_13 : Integer.Sparse Key := [(key750, 720), (key927, -720)]

def entry24_14 : Integer.Sparse Key := [(key30, -720), (key146, 720)]

def entry24_15 : Integer.Sparse Key := [(key1273, 720), (key1696, -720)]

def entry24_16 : Integer.Sparse Key := [(key1357, 720), (key1483, -720)]

def entry24_17 : Integer.Sparse Key := [(key1489, 720), (key1715, -720)]

def entry24_18 : Integer.Sparse Key := [(key118, -720), (key155, 720)]

def entry24_19 : Integer.Sparse Key := [(key1498, 720), (key1730, -720)]

def entry24_20 : Integer.Sparse Key := [(key670, -720), (key680, 720)]

def entry24_21 : Integer.Sparse Key := [(key1710, -720), (key1859, 720)]

def entry24_22 : Integer.Sparse Key := [(key1484, 720), (key1710, -720)]

def entry24_23 : Integer.Sparse Key := [(key1277, 720), (key1700, -720)]

def entry24_24 : Integer.Sparse Key := [(key288, 720), (key513, -720)]

def entry25_0 : Integer.Sparse Key := [(key2428, 576), (key2429, -576), (key2496, 144), (key2508, -144), (key2550, -144), (key2556, 144)]

def entry25_1 : Integer.Sparse Key := [(key1132, -720), (key1203, 720)]

def entry25_3 : Integer.Sparse Key := [(key3060, -576), (key3064, 576), (key3095, -144), (key3101, 144), (key3123, 144), (key3125, -144)]

def entry25_4 : Integer.Sparse Key := [(key2415, 144), (key2418, -144), (key2488, -144), (key2493, -576), (key2547, 144), (key2549, 576)]

def entry25_5 : Integer.Sparse Key := [(key2680, 144), (key2683, -144), (key2711, -144), (key2716, -432), (key2741, 144), (key2743, 432), (key2819, -144), (key2901, 144), (key2956, 144), (key2980, -144)]

def entry25_6 : Integer.Sparse Key := [(key3119, -720), (key3127, 720)]

def entry25_7 : Integer.Sparse Key := [(key2711, 144), (key2716, 288), (key2741, -144), (key2743, -288), (key2814, -144), (key2819, -288), (key2901, -288), (key2954, 144), (key2956, 288), (key2980, 288)]

def entry25_8 : Integer.Sparse Key := [(key1406, 144), (key1408, -144), (key1434, -144), (key1437, -432), (key1462, 144), (key1463, 432), (key1586, -144), (key1664, 144), (key1795, 144), (key1822, -144)]

def entry25_9 : Integer.Sparse Key := [(key2680, 432), (key2683, -432), (key2711, 144), (key2716, -144), (key2741, -144), (key2743, 144), (key2814, 144), (key2819, -144), (key2954, -144), (key2956, 144)]

def entry25_10 : Integer.Sparse Key := [(key1431, -576), (key1461, 576), (key1580, -144), (key1663, 144), (key1794, 144), (key1821, -144)]

def entry25_12 : Integer.Sparse Key := [(key2415, 432), (key2418, -432), (key2488, 288), (key2493, 432), (key2547, -288), (key2549, -432)]

def entry25_13 : Integer.Sparse Key := [(key2197, 144), (key2198, -144), (key2308, -144), (key2309, -576), (key2345, 144), (key2346, 576)]

def entry25_16 : Integer.Sparse Key := [(key3060, 432), (key3064, -432), (key3095, -432), (key3101, 432), (key3123, -288), (key3125, 288)]

def entry25_17 : Integer.Sparse Key := [(key2693, 288), (key2694, -288), (key2719, -288), (key2731, -288), (key2744, 288), (key2750, 288), (key2834, -144), (key2907, 144), (key2963, 144), (key2986, -144)]

def entry25_18 : Integer.Sparse Key := [(key1064, 576), (key1065, -576), (key1144, 144), (key1158, -144), (key1208, -144), (key1215, 144)]

def entry25_19 : Integer.Sparse Key := [(key3085, -720), (key3087, 720)]

def entry25_20 : Integer.Sparse Key := [(key1943, 720), (key1944, -720)]

def entry25_21 : Integer.Sparse Key := [(key2679, 216), (key2682, -144), (key2689, -48), (key2710, 72), (key2715, -144), (key2742, 72), (key2813, 48), (key2818, -144), (key2955, 48), (key3047, 216), (key3050, -288), (key3054, 48), (key3061, 72), (key3066, -144), (key3072, 72), (key3096, 96), (key3103, -144), (key3110, 96)]

def entry25_22 : Integer.Sparse Key := [(key2679, 72), (key2682, -144), (key2689, -48), (key2710, -144), (key2715, -432), (key2740, 144), (key2742, 360), (key2818, -144), (key2900, 144), (key2955, 48), (key2979, -144), (key3047, 72), (key3054, 48), (key3072, 72), (key3110, 96)]

def entry25_23 : Integer.Sparse Key := [(key2428, 288), (key2429, -288), (key2496, -288), (key2508, -432), (key2550, 288), (key2556, 432)]

def entry25_24 : Integer.Sparse Key := [(key1731, -720), (key1873, 720)]

def entry26_0 : Integer.Sparse Key := [(key1280, 96), (key1286, -96), (key1703, 144), (key1707, -96), (key1757, 96), (key1760, -144), (key1856, 96), (key1858, -144), (key1887, 144), (key1890, -96)]

def entry26_1 : Integer.Sparse Key := [(key501, -720), (key557, 720)]

def entry26_2 : Integer.Sparse Key := [(key226, 48), (key232, -48), (key498, -288), (key504, -240), (key552, 240), (key562, 288), (key666, -192), (key683, 192)]

def entry26_3 : Integer.Sparse Key := [(key1368, -192), (key1377, 192), (key1494, -48), (key1516, 48), (key1720, -240), (key1726, 288), (key1744, -288), (key1755, 240)]

def entry26_4 : Integer.Sparse Key := [(key1279, 48), (key1285, -48), (key1702, -288), (key1708, -240), (key1752, 240), (key1758, 288), (key1935, -192), (key1955, 192)]

def entry26_5 : Integer.Sparse Key := [(key1365, -96), (key1371, -96), (key1375, 96), (key1380, 96), (key1497, -48), (key1514, 48), (key1717, -144), (key1724, 144), (key1729, 48), (key1742, -48), (key1748, -144), (key1759, 144), (key1939, -96), (key1942, 96), (key1951, -96), (key1956, 96)]

def entry26_6 : Integer.Sparse Key := [(key1705, -720), (key1754, 720)]

def entry26_7 : Integer.Sparse Key := [(key1365, 96), (key1371, 48), (key1375, -48), (key1380, -96), (key1491, -96), (key1497, -48), (key1514, 48), (key1520, 96), (key1724, -192), (key1729, -192), (key1742, 192), (key1748, 192), (key1942, -192), (key1951, 192)]

def entry26_8 : Integer.Sparse Key := [(key284, -96), (key287, -96), (key293, 96), (key299, 96), (key356, -48), (key370, 48), (key510, -144), (key521, 144), (key526, 48), (key542, -48), (key546, -144), (key563, 144), (key669, -96), (key673, 96), (key679, -96), (key684, 96)]

def entry26_9 : Integer.Sparse Key := [(key1365, 96), (key1371, -96), (key1375, 96), (key1380, -96), (key1491, 96), (key1497, -96), (key1514, 96), (key1520, -96), (key1717, 48), (key1724, 144), (key1729, -144), (key1742, 144), (key1748, -144), (key1759, -48), (key1939, -48), (key1956, 48)]

def entry26_10 : Integer.Sparse Key := [(key286, -192), (key297, 192), (key355, -48), (key372, 48), (key512, -240), (key525, 288), (key545, -288), (key558, 240)]

def entry26_11 : Integer.Sparse Key := [(key1281, 144), (key1285, -144), (key1704, 576), (key1758, -576), (key1857, 144), (key1888, -144)]

def entry26_12 : Integer.Sparse Key := [(key1279, 144), (key1285, -144), (key1702, 576), (key1758, -576), (key1935, 144), (key1955, -144)]

def entry26_13 : Integer.Sparse Key := [(key732, 48), (key734, -48), (key866, -288), (key868, -240), (key882, -192), (key900, 240), (key901, 288), (key913, 192)]

def entry26_14 : Integer.Sparse Key := [(key226, 144), (key232, -144), (key498, 576), (key562, -576), (key666, 144), (key683, -144)]

def entry26_15 : Integer.Sparse Key := [(key1281, 48), (key1285, -48), (key1704, -288), (key1708, -240), (key1753, 240), (key1758, 288), (key1857, -192), (key1888, 192)]

def entry26_16 : Integer.Sparse Key := [(key1368, 144), (key1377, -144), (key1494, -144), (key1516, 144), (key1726, -576), (key1744, 576)]

def entry26_17 : Integer.Sparse Key := [(key1370, -192), (key1379, 192), (key1492, 48), (key1496, -96), (key1519, 96), (key1522, -48), (key1718, -48), (key1728, 96), (key1747, -96), (key1761, 48), (key1865, -192), (key1870, 192), (key1883, -192), (key1891, 192)]

def entry26_18 : Integer.Sparse Key := [(key227, 96), (key233, -96), (key499, 144), (key503, -96), (key560, 96), (key564, -144), (key623, 96), (key625, -144), (key649, 144), (key653, -96)]

def entry26_19 : Integer.Sparse Key := [(key1505, -240), (key1517, 240), (key1738, -240), (key1745, 240)]

def entry26_20 : Integer.Sparse Key := [(key514, 720), (key519, -720)]

def entry26_21 : Integer.Sparse Key := [(key1367, 96), (key1371, -96), (key1376, 96), (key1380, -96), (key1493, 96), (key1497, -96), (key1515, 96), (key1520, -96), (key1719, 48), (key1725, 144), (key1729, -144), (key1743, 144), (key1748, -144), (key1759, -48), (key1866, -48), (key1889, 48)]

def entry26_22 : Integer.Sparse Key := [(key1367, -96), (key1371, -96), (key1376, 96), (key1380, 96), (key1497, -48), (key1515, 48), (key1719, -144), (key1725, 144), (key1729, 48), (key1743, -48), (key1748, -144), (key1759, 144), (key1866, -96), (key1871, 96), (key1881, -96), (key1889, 96)]

def entry26_23 : Integer.Sparse Key := [(key1280, 48), (key1286, -48), (key1703, -48), (key1707, -288), (key1757, 288), (key1760, 48), (key1856, -192), (key1858, -192), (key1887, 192), (key1890, 192)]

def entry26_24 : Integer.Sparse Key := [(key524, -720), (key555, 720)]

def entry26_25 : Integer.Sparse Key := [(key1508, 576), (key1510, -576), (key1737, 144), (key1749, -144), (key1876, -144), (key1882, 144)]

def entry26_26 : Integer.Sparse Key := [(key291, 96), (key298, -96), (key518, 144), (key522, -96), (key553, 64), (key561, -192), (key631, 128), (key632, -96), (key647, 144), (key650, -96)]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9765 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9766 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9767 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9768 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9769 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9770 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9771 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9772 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9773 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9774 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9775 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9776 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

def row9777 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9778 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9779 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9780 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9781 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9782 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9783 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9784 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9785 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9786 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9787 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9788 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

def row9789 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9790 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9791 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9792 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9793 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9794 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9795 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9796 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9797 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9798 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9799 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9800 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

def row9801 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9802 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9803 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9804 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9805 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9806 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9807 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9808 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9809 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9810 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9811 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9812 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

def row9813 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9814 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

def row9815 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6645 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6646 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6647 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6648 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row6649 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row6650 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2732, -2), (key2798, -2), (key2829, 2), (key2835, -2), (key2885, 4), (key2927, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3010, 2), (key3030, -2)]

def row6651 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2927, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3030, 1)]

def row6652 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2927, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3030, 1)]

def row6653 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2660, 2), (key2667, -2), (key2676, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2732, -2), (key2747, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2885, 4), (key2927, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3030, -2)]

def row6654 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2747, -1), (key2798, 1), (key2835, 1), (key2885, -2), (key2927, 1), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key3030, 1)]

def row6655 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2747, -1), (key2798, 1), (key2835, 1), (key2885, -2), (key2927, 1), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key3030, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6656 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2728, 1), (key2732, 1), (key2735, 1), (key2747, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2936, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

def row6657 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2728, 1), (key2732, 1), (key2735, 1), (key2747, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2936, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

def row6658 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2640, -1), (key2641, 1), (key2644, 1), (key2646, 1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2794, 1), (key2798, 1), (key2835, 1), (key2885, -2), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

def row6659 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2640, -1), (key2641, 1), (key2644, 1), (key2646, 1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2794, 1), (key2798, 1), (key2835, 1), (key2885, -2), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

def row6660 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2653, 2), (key2667, -1), (key2671, -1), (key2676, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2732, -2), (key2747, 2), (key2798, -2), (key2829, 1), (key2835, -2), (key2885, 4), (key2936, 1), (key2948, 1), (key2972, -4), (key2976, 2), (key2983, 2), (key2998, -2), (key3000, -2)]

def row6661 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2653, 2), (key2667, -1), (key2671, -1), (key2676, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2732, -2), (key2747, 2), (key2798, -2), (key2829, 1), (key2835, -2), (key2885, 4), (key2936, 1), (key2948, 1), (key2972, -4), (key2976, 2), (key2983, 2), (key2998, -2), (key3000, -2)]

def row6662 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6663 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6664 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6665 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6666 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6667 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6668 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6669 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6670 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6671 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6672 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6673 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6674 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6675 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

def row6676 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

def row6677 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7348 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7349 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7350 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7351 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 4), (key2525, -4), (key2533, -2), (key2562, 4)]

def row7352 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 4), (key2525, -4), (key2533, -2), (key2562, 4)]

def row7353 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 4), (key2525, -4), (key2533, -2), (key2562, 4)]

def row7354 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7355 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7356 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 2), (key2525, -4), (key2532, 2), (key2533, -2), (key2562, 4)]

def row7357 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2521, 2), (key2525, -4), (key2532, 2), (key2533, -2), (key2562, 4)]

def row7358 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7359 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, -4), (key2525, -4), (key2532, 4), (key2533, -2), (key2562, 4)]

def row7360 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7361 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7362 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7363 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7364 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7365 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -4), (key2525, 4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7366 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -4), (key2525, 4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7367 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7368 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2521, -2), (key2525, 4), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7369 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7370 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7371 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -4), (key2525, 4), (key2532, -4), (key2533, 2), (key2562, -2), (key2564, 4)]

def row7382 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

def row7383 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

def row7384 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

def row7385 : Integer.Sparse Key := [(key1090, 12), (key1098, 6), (key1169, 6), (key1180, -6), (key1183, -12), (key1220, -6)]

def row7398 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

def row7399 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

def row7400 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

def row7401 : Integer.Sparse Key := [(key3, -24), (key86, 18), (key147, 6)]

def row7414 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

def row7415 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

def row7416 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

def row7417 : Integer.Sparse Key := [(key1, -6), (key7, -18), (key84, 6), (key90, 12), (key151, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7430 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

def row7431 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

def row7432 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

def row7433 : Integer.Sparse Key := [(key2377, 6), (key2389, -6), (key2471, 6), (key2479, -12), (key2502, 12), (key2518, -6)]

def row7446 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

def row7447 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

def row7448 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

def row7449 : Integer.Sparse Key := [(key989, 6), (key1024, -24), (key1102, 18)]

def row7462 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

def row7463 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

def row7464 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

def row7465 : Integer.Sparse Key := [(key995, 6), (key1030, -18), (key1067, -6), (key1108, 12), (key1146, 6)]

def row7478 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

def row7479 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

def row7480 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

def row7481 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2696, 6), (key2799, -18), (key2849, 12)]

def row7510 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

def row7511 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

def row7512 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

def row7513 : Integer.Sparse Key := [(key970, -24), (key1084, 18), (key1226, 6)]

def row7526 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

def row7527 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

def row7528 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

def row7529 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1228, 6)]

def row7542 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

def row7543 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

def row7544 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

def row7545 : Integer.Sparse Key := [(key2400, -18), (key2432, -6), (key2466, 12), (key2475, 6), (key2498, 6)]

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

def row7558 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

def row7559 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

def row7560 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

def row7561 : Integer.Sparse Key := [(key2353, -6), (key2359, -18), (key2448, 6), (key2454, 12), (key2515, 6)]

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

def row8517 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

def row8518 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

def row8519 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

def row8520 : Integer.Sparse Key := [(key20, 6), (key45, -18), (key70, -6), (key102, 12), (key133, 6)]

def row8521 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8522 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8523 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8524 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8525 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8526 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8527 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8528 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8529 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8530 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8531 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8532 : Integer.Sparse Key := [(key20, 4), (key31, 2), (key45, 4), (key70, 2), (key102, -8), (key111, -2), (key133, -2)]

def row8533 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

def row8534 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

def row8535 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

def row8536 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1415, 6), (key1564, -18), (key1613, 12)]

def row8537 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8538 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8539 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8540 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8541 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8542 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8543 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8544 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8545 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8546 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8547 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8548 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, 2), (key1415, 4), (key1537, -2), (key1564, 4), (key1613, -8)]

def row8549 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

def row8550 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

def row8551 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

def row8552 : Integer.Sparse Key := [(key1250, 6), (key1525, -18), (key1603, 12), (key1892, -6), (key1914, 6)]

def row8553 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8554 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8555 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8556 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8557 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8558 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8559 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8560 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8561 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8562 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8563 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8564 : Integer.Sparse Key := [(key1250, 4), (key1269, 2), (key1525, 4), (key1603, -8), (key1677, -2), (key1892, 2), (key1914, -2)]

def row8565 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

def row8566 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

def row8567 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

def row8568 : Integer.Sparse Key := [(key1289, -6), (key1309, 6), (key1417, 6), (key1566, -12), (key1615, 6), (key1902, -6), (key1917, 6)]

def row8569 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8570 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8571 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8572 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8573 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8574 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8575 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8576 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8577 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8578 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8579 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8580 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, 2), (key1417, 2), (key1471, 2), (key1539, -2), (key1566, 2), (key1615, -4), (key1680, -2), (key1902, 2), (key1917, -2)]

def row8581 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

def row8582 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

def row8583 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

def row8584 : Integer.Sparse Key := [(key1248, 6), (key1523, -24), (key1601, 18)]

def row8585 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8586 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8587 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8588 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8589 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8590 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8591 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8592 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8593 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8594 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8595 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8596 : Integer.Sparse Key := [(key1248, 6), (key1523, 6), (key1601, -12)]

def row8661 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

def row8662 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

def row8663 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

def row8664 : Integer.Sparse Key := [(key2456, 12), (key2459, 6), (key2517, -6), (key2520, -12), (key2531, 6), (key2561, -6)]

def row8665 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

def row8666 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

def row8667 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

def row8668 : Integer.Sparse Key := [(key2361, -6), (key2364, 6), (key2456, -12), (key2459, 6), (key2517, -6), (key2520, 12)]

def row8669 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

def row8670 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

def row8671 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

def row8672 : Integer.Sparse Key := [(key969, -24), (key1083, 18), (key1177, 6)]

def row8673 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

def row8674 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

def row8675 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

def row8676 : Integer.Sparse Key := [(key969, 6), (key1083, 18), (key1177, -24)]

def row8677 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

def row8678 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

def row8679 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

def row8680 : Integer.Sparse Key := [(key972, -6), (key977, -18), (key1086, 6), (key1091, 12), (key1181, 6)]

def row8681 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

def row8682 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

def row8683 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

def row8684 : Integer.Sparse Key := [(key977, 6), (key1091, 12), (key1162, 6), (key1181, -18), (key1218, -6)]

def row8685 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

def row8686 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

def row8687 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

def row8688 : Integer.Sparse Key := [(key2397, -18), (key2431, -6), (key2463, 12), (key2474, 6), (key2497, 6)]

def row8689 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

def row8690 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

def row8691 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

def row8692 : Integer.Sparse Key := [(key2369, 6), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, -18)]

def row8693 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

def row8694 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

def row8695 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

def row8696 : Integer.Sparse Key := [(key2354, -6), (key2358, -18), (key2449, 6), (key2453, 12), (key2529, 6)]

def row8697 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

def row8698 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

def row8699 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

def row8700 : Integer.Sparse Key := [(key2358, 6), (key2453, 12), (key2514, 6), (key2529, -18), (key2559, -6)]

def row8701 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

def row8702 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

def row8703 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8704 : Integer.Sparse Key := [(key2763, -6), (key2767, -12), (key2840, 6), (key2844, 6), (key2888, 6), (key2930, -6), (key2967, 6)]

def row8705 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

def row8706 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

def row8707 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

def row8708 : Integer.Sparse Key := [(key2588, 6), (key2599, -6), (key2767, 6), (key2844, 6), (key2875, 6), (key2888, -12), (key2909, -6)]

def row8709 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

def row8710 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

def row8711 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

def row8712 : Integer.Sparse Key := [(key2352, -24), (key2447, 18), (key2511, 6)]

def row8713 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

def row8714 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

def row8715 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

def row8716 : Integer.Sparse Key := [(key2352, 6), (key2447, 18), (key2511, -24)]

def row8725 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8726 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8727 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8728 : Integer.Sparse Key := [(key1527, -6), (key1532, -12), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, -6), (key1807, 6)]

def row8729 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8730 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8731 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8732 : Integer.Sparse Key := [(key1257, 6), (key1266, -6), (key1532, 6), (key1610, 6), (key1638, 6), (key1649, -12), (key1672, -6)]

def row8741 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

def row8742 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

def row8743 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

def row8744 : Integer.Sparse Key := [(key1524, -18), (key1602, 12), (key1645, 6), (key1762, -6), (key1803, 6)]

def row8745 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

def row8746 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

def row8747 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

def row8748 : Integer.Sparse Key := [(key1249, 6), (key1262, -6), (key1524, 6), (key1602, 12), (key1645, -18)]

def row8749 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

def row8750 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

def row8751 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

def row8752 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2527, -18), (key2558, -6)]

def row8753 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

def row8754 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

def row8755 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

def row8756 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2527, 18), (key2558, 6)]

def row8761 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

def row8762 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

def row8763 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

def row8764 : Integer.Sparse Key := [(key970, 6), (key1084, 18), (key1226, -24)]

def row8765 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

def row8766 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

def row8767 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

def row8768 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, 6), (key1228, -18), (key1245, -6)]

def row8769 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

def row8770 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

def row8771 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

def row8772 : Integer.Sparse Key := [(key2372, 6), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, -18)]

def row8773 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

def row8774 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

def row8775 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

def row8776 : Integer.Sparse Key := [(key2359, 6), (key2454, 12), (key2515, 6), (key2566, -18), (key2578, -6)]

def row8785 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

def row8786 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

def row8787 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

def row8788 : Integer.Sparse Key := [(key2355, -24), (key2450, 18), (key2512, 6)]

def row8789 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

def row8790 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

def row8791 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

def row8792 : Integer.Sparse Key := [(key2355, 6), (key2450, 18), (key2512, -24)]

def row8793 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

def row8794 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

def row8795 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

def row8796 : Integer.Sparse Key := [(key2370, -6), (key2376, -12), (key2388, -6), (key2398, 6), (key2404, 12), (key2435, 6)]

def row8797 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

def row8798 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

def row8799 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

def row8800 : Integer.Sparse Key := [(key2604, 6), (key2916, 12), (key2925, 6), (key3005, -6), (key3019, -12), (key3028, -6)]

def row8801 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

def row8802 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

def row8803 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

def row8804 : Integer.Sparse Key := [(key1526, -6), (key1534, -12), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, -6), (key1916, 6)]

def row8805 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

def row8806 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

def row8807 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

def row8808 : Integer.Sparse Key := [(key1259, 6), (key1271, -6), (key1534, 6), (key1612, 6), (key1640, 6), (key1679, -12), (key1693, -6)]

def row8817 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

def row8818 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

def row8819 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

def row8820 : Integer.Sparse Key := [(key1525, -18), (key1603, 12), (key1677, 6), (key1892, -6), (key1914, 6)]

def row8821 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

def row8822 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

def row8823 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

def row8824 : Integer.Sparse Key := [(key1250, 6), (key1269, -6), (key1525, 6), (key1603, 12), (key1677, -18)]

def row8825 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

def row8826 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

def row8827 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

def row8828 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2529, -18), (key2559, -6)]

def row8829 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

def row8830 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

def row8831 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8832 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

def row8833 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

def row8834 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

def row8835 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

def row8836 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

def row8837 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

def row8838 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

def row8839 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

def row8840 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

def row8841 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

def row8842 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

def row8843 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

def row8844 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

def row8845 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8846 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8847 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8848 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8849 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8850 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8851 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8852 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8853 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8854 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8855 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8856 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

def row8857 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

def row8858 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

def row8859 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

def row8860 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

def row8861 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8862 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8863 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8864 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8865 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8866 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8867 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8868 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8869 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8870 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8871 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8872 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

def row8873 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

def row8874 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

def row8875 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

def row8876 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

def row8877 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8878 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8879 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8880 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8881 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8882 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8883 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8884 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8885 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8886 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8887 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8888 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

def row8889 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

def row8890 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

def row8891 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

def row8892 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

def row8893 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8894 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8895 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8896 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8897 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8898 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8899 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8900 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8901 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8902 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8903 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8904 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

def row8905 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

def row8906 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

def row8907 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

def row8908 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

def row8909 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8910 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8911 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8912 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8913 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8914 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8915 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8916 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8917 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8918 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8919 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8920 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

def row8921 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

def row8922 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

def row8923 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

def row8924 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

def row8925 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8926 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8927 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8928 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8929 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8930 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8931 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8932 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8933 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8934 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8935 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8936 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

def row8937 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

def row8938 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

def row8939 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

def row8940 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

def row8941 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8942 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8943 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8944 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8945 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8946 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8947 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8948 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8949 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8950 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8951 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

def row8952 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row8969 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

def row8970 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

def row8971 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

def row8972 : Integer.Sparse Key := [(key817, -6), (key818, -12), (key825, -6), (key897, 6), (key898, 6), (key902, 6), (key908, 6)]

def row8973 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8974 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8975 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8976 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8977 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8978 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8979 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8980 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8981 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8982 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8983 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8984 : Integer.Sparse Key := [(key738, -2), (key743, 2), (key817, 2), (key818, 2), (key825, 2), (key897, -2), (key898, -4), (key902, 2), (key908, -2), (key960, -2), (key962, 2)]

def row8985 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

def row8986 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

def row8987 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

def row8988 : Integer.Sparse Key := [(key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6), (key2341, -12), (key2343, -6), (key2347, -6)]

def row9001 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

def row9002 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

def row9003 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

def row9004 : Integer.Sparse Key := [(key843, -18), (key844, -6), (key943, 12), (key944, 6), (key945, 6)]

def row9005 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9006 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9007 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9008 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9009 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9010 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9011 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9012 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9013 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9014 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9015 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9016 : Integer.Sparse Key := [(key754, -2), (key755, 2), (key843, 4), (key844, 2), (key943, -8), (key944, 4), (key945, -2)]

def row9017 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

def row9018 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

def row9019 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

def row9020 : Integer.Sparse Key := [(key2006, 6), (key2007, 18), (key2340, -18), (key2349, -6)]

def row9021 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9022 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9023 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9024 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9025 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9026 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9027 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9028 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9029 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9030 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9031 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9032 : Integer.Sparse Key := [(key2007, -6), (key2299, 6), (key2313, -6), (key2340, 6)]

def row9033 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

def row9034 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

def row9035 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

def row9036 : Integer.Sparse Key := [(key1998, 6), (key2000, 18), (key2340, -18), (key2349, -6)]

def row9037 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9038 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9039 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9040 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9041 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9042 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9043 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9044 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9045 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9046 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9047 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9048 : Integer.Sparse Key := [(key2000, -6), (key2267, 6), (key2292, -6), (key2340, 6)]

def row9049 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

def row9050 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

def row9051 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

def row9052 : Integer.Sparse Key := [(key776, -6), (key778, -18), (key801, 6), (key803, 12), (key811, 6)]

def row9053 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

def row9054 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

def row9055 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

def row9056 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

def row9057 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

def row9058 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, 2), (key839, 2)]

def row9059 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, 2), (key839, 2)]

def row9060 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

def row9061 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key836, 2), (key839, 2)]

def row9062 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

def row9063 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

def row9064 : Integer.Sparse Key := [(key776, 2), (key778, 4), (key801, -2), (key803, -8), (key811, -2), (key836, 4), (key839, 2)]

def row9065 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

def row9066 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

def row9067 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

def row9068 : Integer.Sparse Key := [(key976, -6), (key984, 6), (key1090, -12), (key1098, 6), (key1180, -6), (key1183, 12)]

def row9069 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

def row9070 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

def row9071 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

def row9072 : Integer.Sparse Key := [(key3, 6), (key86, 18), (key147, -24)]

def row9073 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

def row9074 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

def row9075 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

def row9076 : Integer.Sparse Key := [(key7, 6), (key90, 12), (key151, 6), (key193, -18), (key202, -6)]

def row9077 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

def row9078 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

def row9079 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

def row9080 : Integer.Sparse Key := [(key1030, -18), (key1067, -6), (key1108, 12), (key1119, 6), (key1146, 6)]

def row9081 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

def row9082 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

def row9083 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

def row9084 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, -18)]

def row9085 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

def row9086 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

def row9087 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9088 : Integer.Sparse Key := [(key971, -6), (key979, -18), (key1085, 6), (key1093, 12), (key1164, 6)]

def row9089 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

def row9090 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

def row9091 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

def row9092 : Integer.Sparse Key := [(key979, 6), (key1093, 12), (key1164, -18), (key1228, 6), (key1245, -6)]

def row9093 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

def row9094 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

def row9095 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

def row9096 : Integer.Sparse Key := [(key1028, -6), (key1036, -12), (key1071, -6), (key1106, 6), (key1114, 6), (key1123, 6), (key1150, 6)]

def row9097 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

def row9098 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

def row9099 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

def row9100 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, 6), (key1114, 6), (key1123, -12), (key1232, 6), (key1235, -6)]

def row9101 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

def row9102 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

def row9103 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

def row9104 : Integer.Sparse Key := [(key973, -24), (key1087, 18), (key1160, 6)]

def row9105 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

def row9106 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

def row9107 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

def row9108 : Integer.Sparse Key := [(key973, 6), (key1087, 18), (key1160, -24)]

def row9109 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

def row9110 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

def row9111 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

def row9112 : Integer.Sparse Key := [(key993, -6), (key1001, -12), (key1015, -6), (key1028, 6), (key1036, 12), (key1071, 6)]

def row9129 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

def row9130 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

def row9131 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

def row9132 : Integer.Sparse Key := [(key993, -6), (key1001, 6), (key1028, -6), (key1036, 6), (key1106, -12), (key1114, 6), (key1232, 6)]

def row9133 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

def row9134 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

def row9135 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

def row9136 : Integer.Sparse Key := [(key45, -18), (key70, -6), (key102, 12), (key111, 6), (key133, 6)]

def row9137 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

def row9138 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

def row9139 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

def row9140 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, 6), (key102, 12), (key111, -18)]

def row9141 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

def row9142 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

def row9143 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

def row9144 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1181, -18), (key1218, -6)]

def row9145 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

def row9146 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

def row9147 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

def row9148 : Integer.Sparse Key := [(key972, -6), (key1086, -18), (key1162, 18), (key1218, 6)]

def row9149 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

def row9150 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

def row9151 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

def row9152 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1228, -18), (key1245, -6)]

def row9153 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

def row9154 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

def row9155 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

def row9156 : Integer.Sparse Key := [(key971, -6), (key1085, -18), (key1164, 18), (key1245, 6)]

def row9157 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

def row9158 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

def row9159 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

def row9160 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key959, 6)]

def row9161 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

def row9162 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

def row9163 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

def row9164 : Integer.Sparse Key := [(key715, 6), (key892, 12), (key914, 6), (key959, -18), (key966, -6)]

def row9165 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

def row9166 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

def row9167 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

def row9168 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key193, -18), (key202, -6)]

def row9169 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

def row9170 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

def row9171 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

def row9172 : Integer.Sparse Key := [(key1, -6), (key84, -18), (key193, 18), (key202, 6)]

def row9173 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9174 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9175 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9176 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9177 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9178 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9179 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9180 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9181 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9182 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9183 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9184 : Integer.Sparse Key := [(key2361, 2), (key2364, -2), (key2459, -4), (key2517, 4), (key2531, -2), (key2561, 2)]

def row9185 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9186 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9187 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9188 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9189 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9190 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9191 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9192 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9193 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9194 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9195 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9196 : Integer.Sparse Key := [(key969, 6), (key1083, -12), (key1177, 6)]

def row9197 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9198 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9199 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9200 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9201 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9202 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9203 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9204 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9205 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9206 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9207 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9208 : Integer.Sparse Key := [(key972, 2), (key977, 4), (key1086, -2), (key1091, -8), (key1162, -2), (key1181, 4), (key1218, 2)]

def row9209 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9210 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9211 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9212 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9213 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9214 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9215 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9216 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9217 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9218 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9219 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9220 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

def row9221 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9222 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9223 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9224 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9225 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9226 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9227 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9228 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9229 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9230 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9231 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9232 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

def row9233 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9234 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9235 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9236 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9237 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9238 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9239 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9240 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9241 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9242 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9243 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9244 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

def row9245 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9246 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9247 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9248 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9249 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9250 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9251 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9252 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9253 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9254 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9255 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9256 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

def row9269 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9270 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9271 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9272 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9273 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9274 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9275 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9276 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9277 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9278 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9279 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9280 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

def row9293 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9294 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9295 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9296 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9297 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9298 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9299 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9300 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9301 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9302 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9303 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9304 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

def row9305 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9306 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9307 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9308 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9309 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9310 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9311 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9312 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9313 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9314 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9315 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9316 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

def row9317 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

def row9318 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

def row9319 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

def row9320 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

def row9321 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9322 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9323 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9324 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9325 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9326 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9327 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9328 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9329 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9330 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9331 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9332 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

def row9333 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

def row9334 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

def row9335 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

def row9336 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

def row9337 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9338 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9339 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9340 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9341 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9342 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9343 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9344 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9345 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9346 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9347 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9348 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

def row9349 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

def row9350 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

def row9351 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

def row9352 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1162, -18), (key1218, -6)]

def row9353 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9354 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9355 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9356 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9357 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9358 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9359 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9360 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9361 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9362 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9363 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9364 : Integer.Sparse Key := [(key977, -6), (key1086, 6), (key1162, 6), (key1181, -6)]

def row9365 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

def row9366 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

def row9367 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

def row9368 : Integer.Sparse Key := [(key2353, -6), (key2356, -18), (key2448, 6), (key2451, 12), (key2513, 6)]

def row9369 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

def row9370 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

def row9371 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

def row9372 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

def row9373 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

def row9374 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, 2), (key2558, 2)]

def row9375 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, 2), (key2558, 2)]

def row9376 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

def row9377 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2527, 2), (key2558, 2)]

def row9378 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

def row9379 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

def row9380 : Integer.Sparse Key := [(key2353, 2), (key2356, 4), (key2448, -2), (key2451, -8), (key2513, -2), (key2527, 4), (key2558, 2)]

def row9381 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

def row9382 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

def row9383 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

def row9384 : Integer.Sparse Key := [(key2405, 6), (key2436, -6), (key2471, 6), (key2479, 12), (key2502, -12), (key2518, -6)]

def row9385 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

def row9386 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

def row9387 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

def row9388 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 18)]

def row9389 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

def row9390 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

def row9391 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

def row9392 : Integer.Sparse Key := [(key995, -18), (key1011, -6), (key1030, 6), (key1108, 12), (key1119, 6)]

def row9393 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

def row9394 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

def row9395 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

def row9396 : Integer.Sparse Key := [(key2661, -6), (key2696, -18), (key2776, 6), (key2799, 6), (key2849, 12)]

def row9397 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

def row9398 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

def row9399 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

def row9400 : Integer.Sparse Key := [(key2372, -18), (key2385, -6), (key2400, 6), (key2466, 12), (key2475, 6)]

def row9401 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

def row9402 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

def row9403 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

def row9404 : Integer.Sparse Key := [(key2372, 6), (key2400, -18), (key2432, -6), (key2466, 12), (key2498, 6)]

def row9405 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

def row9406 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

def row9407 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

def row9408 : Integer.Sparse Key := [(key2665, -6), (key2700, 6), (key2780, -12), (key2789, -6), (key2803, 6), (key2853, 6), (key2855, 6)]

def row9409 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

def row9410 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

def row9411 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

def row9412 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2780, 6), (key2803, -12), (key2824, -6), (key2853, 6), (key2865, 6)]

def row9413 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

def row9414 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

def row9415 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

def row9416 : Integer.Sparse Key := [(key2368, -24), (key2760, 6), (key2837, 18)]

def row9417 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

def row9418 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

def row9419 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

def row9420 : Integer.Sparse Key := [(key2396, -24), (key2581, 6), (key2837, 18)]

def row9445 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

def row9446 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

def row9447 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

def row9448 : Integer.Sparse Key := [(key1382, -6), (key1415, 6), (key1537, -18), (key1564, 6), (key1613, 12)]

def row9449 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

def row9450 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

def row9451 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

def row9452 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1537, 6), (key1564, -18), (key1613, 12)]

def row9453 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

def row9454 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

def row9455 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

def row9456 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2431, -6), (key2497, -18)]

def row9457 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

def row9458 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

def row9459 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

def row9460 : Integer.Sparse Key := [(key2384, -6), (key2397, 18), (key2431, 6), (key2474, -18)]

def row9461 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

def row9462 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

def row9463 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

def row9464 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2432, -6), (key2498, -18)]

def row9465 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

def row9466 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

def row9467 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

def row9468 : Integer.Sparse Key := [(key2385, -6), (key2400, 18), (key2432, 6), (key2475, -18)]

def row9469 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

def row9470 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

def row9471 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row9472 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

def row9473 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

def row9474 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

def row9475 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

def row9476 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

def row9477 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

def row9478 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

def row9479 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

def row9480 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

def row9481 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

def row9482 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

def row9483 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

def row9484 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

def row9485 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

def row9486 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

def row9487 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

def row9488 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

def row9489 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

def row9490 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

def row9491 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

def row9492 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

def row9493 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

def row9494 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

def row9495 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

def row9496 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

def row9497 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

def row9498 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

def row9499 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

def row9500 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

def row9501 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9502 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9503 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9504 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9505 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9506 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9507 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9508 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9509 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9510 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9511 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9512 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

def row9513 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2933, 4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

def row9514 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2933, 4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

def row9515 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2933, 4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

def row9516 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2592, 2), (key2595, -4), (key2602, 4), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

def row9517 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2592, 2), (key2595, -4), (key2602, 4), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

def row9518 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2592, 2), (key2595, -4), (key2602, 4), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

def row9519 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2441, 2), (key2544, 2), (key2555, 2), (key2565, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2933, 2), (key2934, -2), (key2991, 2), (key2993, -4)]

def row9520 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2441, 2), (key2544, 2), (key2555, 2), (key2565, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2933, 2), (key2934, -2), (key2991, 2), (key2993, -4)]

def row9521 : Integer.Sparse Key := [(key2393, 2), (key2407, 2), (key2441, 4), (key2544, 2), (key2555, 2), (key2565, 4), (key2592, 2), (key2595, -4), (key2602, 2), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2934, -2), (key2991, 2), (key2993, -4)]

def row9522 : Integer.Sparse Key := [(key2393, 2), (key2407, 2), (key2441, 4), (key2544, 2), (key2555, 2), (key2565, 4), (key2592, 2), (key2595, -4), (key2602, 2), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2934, -2), (key2991, 2), (key2993, -4)]

def row9523 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2914, -4), (key2934, -2), (key2993, -4)]

def row9524 : Integer.Sparse Key := [(key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, 2), (key2595, -4), (key2603, -2), (key2774, -4), (key2882, -4), (key2914, -4), (key2934, -2), (key2993, -4)]

def row9525 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9526 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9527 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9528 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9529 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9530 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9531 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9532 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9533 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9534 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9535 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9536 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

def row9537 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9538 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9539 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9540 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9541 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9542 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9543 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9544 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9545 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9546 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9547 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

def row9548 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

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

def nodeValue1012 : Sparse Master := [(Sum.inr 1012, (1 / 1))]

def nodeValue1014 : Sparse Master := [(Sum.inr 1014, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


