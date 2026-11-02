-- Prove2me | Definitions.Def_OAIQ106D087
-- name    : OAIQ106D087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:57:08.571094+00:00
-- url     : https://prove2.me/theorems/ccf73ecb-3060-43bc-849f-e160ea37c0ed
-- title:
--   Definitions bundle OAIQ106D087 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 894 declarations of OpenAI's Lean: 894 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block2.entry0_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_10`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_8`, `OAI.MUB6.Certificate.GramEntries.Block2.entry10_9`, `OAI.MUB6.Certificate.GramEntries.Block2.entry2_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry2_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry2_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry3_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry4_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry5_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry6_6`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_1`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_5`, `OAI.MUB6.Certificate.GramEntries.Block2.entry7_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entry8_0`, `OAI.MUB6.Certificate.GramEntries.Block2.entry8_2` and 854 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramEntries_Block2Data`, `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block16`, `MutuallyUnbiased_GramKeys_Block17`, `MutuallyUnbiased_GramKeys_Block18`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block6`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block18`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block20`, `MutuallyUnbiased_GramRows_Block21`, `MutuallyUnbiased_GramRows_Block22`, `MutuallyUnbiased_GramRows_Block23`, `MutuallyUnbiased_GramRows_Block24`, `MutuallyUnbiased_GramRows_Block25`, `MutuallyUnbiased_GramRows_Block27`, `MutuallyUnbiased_GramRows_Block28`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_GramRows_Block61`, `MutuallyUnbiased_GramRows_Block62`, `MutuallyUnbiased_GramRows_Block63`, `MutuallyUnbiased_GramRows_Block64`, `MutuallyUnbiased_GramRows_Block78`, `MutuallyUnbiased_GramRows_Block79`, `MutuallyUnbiased_GramRows_Block80`, `MutuallyUnbiased_GramRows_Block81`, `MutuallyUnbiased_MixedSemantics_Values18`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D142`, `OAIQ106D143`, `OAIQ106D144`, `OAIQ106D145`, `OAIQ106D146`, `OAIQ106D147`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D150`, `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D155`, `OAIQ106D156`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D161`, `OAIQ106D162`, `OAIQ106D164`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D168`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172`, `OAIQ106D173`, `OAIQ106D174`, `OAIQ106D175`, `OAIQ106D176`, `OAIQ106D177`, `OAIQ106D178`, `OAIQ106D179`, `OAIQ106D180`, `OAIQ106D181`, `OAIQ106D182`, `OAIQ106D183`, `OAIQ106D184`, `OAIQ106D185` and `OAIQ106D186`.
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

def key10 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key13 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key15 : Key := ⟨0, 0, [(-3, -3), (0, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key25 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key26 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key27 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key37 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key39 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key40 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key50 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key51 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key52 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key66 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 0), (1, 0), (1, 1), (1, 1)]⟩
def key67 : Key := ⟨0, 0, [(-3, -1), (0, -1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key76 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key78 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key79 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key80 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key81 : Key := ⟨0, 0, [(-3, -1), (0, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key93 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key96 : Key := ⟨0, 0, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key105 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 2), (1, 1), (2, 0)]⟩
def key107 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key117 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key119 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key120 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩

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

def key131 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key139 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key141 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key142 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key143 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key144 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key158 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩
def key160 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -1), (1, -1), (1, 1)]⟩
def key163 : Key := ⟨0, 0, [(-3, 0), (0, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key169 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩
def key170 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key178 : Key := ⟨0, 0, [(-3, 1), (0, -1), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key183 : Key := ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key189 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩
def key191 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (1, -1), (1, -1), (1, 1)]⟩
def key192 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key197 : Key := ⟨0, 0, [(-3, 2), (0, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key201 : Key := ⟨0, 0, [(-3, 2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key210 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key213 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 1), (0, 1), (1, 1), (2, 0)]⟩
def key215 : Key := ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key217 : Key := ⟨0, 0, [(-2, -3), (-1, 1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key251 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (2, 2)]⟩

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

def key1323 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩

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

def key1441 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩

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

def key1582 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 1), (2, 2)]⟩

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

def key1908 : Key := ⟨0, 1, [(-2, 2), (-1, -1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩

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

def key1992 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key1995 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key2002 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key2004 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key2005 : Key := ⟨0, 1, [(-1, -3), (-1, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key2031 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key2035 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key2036 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key2038 : Key := ⟨0, 1, [(-1, -2), (-1, -1), (0, 1), (0, 1), (1, 0), (1, 1)]⟩

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

def key2061 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (1, 2)]⟩
def key2064 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 2)]⟩
def key2065 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 1), (1, 1), (1, 1)]⟩
def key2066 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, -1), (0, 2), (1, 0), (1, 1)]⟩
def key2070 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key2071 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key2073 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 1), (0, 1), (1, -1), (1, 1)]⟩
def key2080 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (1, 2)]⟩
def key2081 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 0), (1, 1), (1, 1)]⟩
def key2083 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 1), (1, 0), (1, 1)]⟩
def key2084 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, -1), (0, 2), (1, 0), (1, 0)]⟩
def key2086 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (1, 2)]⟩
def key2088 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 1)]⟩
def key2089 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, 0), (0, 2), (1, -1), (1, 0)]⟩
def key2090 : Key := ⟨0, 1, [(-1, -2), (-1, 1), (0, 1), (0, 1), (1, -1), (1, 0)]⟩
def key2093 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩
def key2094 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩
def key2096 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩
def key2097 : Key := ⟨0, 1, [(-1, -2), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩
def key2150 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (1, 2)]⟩
def key2153 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (1, 2)]⟩
def key2154 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 1), (1, 1), (1, 1)]⟩
def key2155 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -2), (0, 2), (1, 0), (1, 1)]⟩
def key2167 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩
def key2168 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩
def key2170 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 1), (0, 1), (1, -2), (1, 1)]⟩

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

def key2177 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (1, 2)]⟩
def key2178 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 0), (1, 1), (1, 1)]⟩
def key2180 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 1), (1, 0), (1, 1)]⟩
def key2181 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -2), (0, 2), (1, 0), (1, 0)]⟩
def key2188 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩
def key2190 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 1), (1, -2), (1, 1)]⟩
def key2191 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, 0), (0, 2), (1, -2), (1, 0)]⟩
def key2192 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, 1), (0, 1), (1, -2), (1, 0)]⟩
def key2195 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 0), (1, 0), (1, 1)]⟩
def key2196 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, -2), (0, 1), (1, 0), (1, 0)]⟩
def key2201 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, 1)]⟩
def key2202 : Key := ⟨0, 1, [(-1, -1), (-1, 2), (0, 0), (0, 1), (1, -2), (1, 0)]⟩
def key2237 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (1, 1)]⟩
def key2243 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (1, 2)]⟩
def key2247 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (1, 2)]⟩
def key2248 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 2), (1, -1), (1, 1)]⟩
def key2254 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (1, 2)]⟩
def key2255 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 2), (1, -2), (1, 1)]⟩
def key2260 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩
def key2271 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (1, 1)]⟩
def key2273 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 1)]⟩
def key2277 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (1, 2)]⟩
def key2278 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, -1), (1, 1), (1, 1)]⟩
def key2280 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (1, 2)]⟩
def key2282 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 1), (1, -1), (1, 1)]⟩
def key2283 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -2), (0, 2), (1, -1), (1, 0)]⟩
def key2288 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, 2)]⟩
def key2290 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 1), (1, -2), (1, 1)]⟩
def key2291 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, -1), (0, 2), (1, -2), (1, 0)]⟩
def key2295 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 1)]⟩
def key2296 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 2), (1, -2), (1, -1)]⟩
def key2297 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩
def key2298 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 1), (0, 1), (1, -2), (1, -1)]⟩

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

def key2304 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, -1), (1, 0), (1, 1)]⟩
def key2306 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 1)]⟩
def key2307 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -2), (0, 1), (1, -1), (1, 0)]⟩
def key2311 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 1)]⟩
def key2312 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, -1), (0, 1), (1, -2), (1, 0)]⟩
def key2325 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 1)]⟩
def key2326 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 0)]⟩
def key2329 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, -1), (1, 0), (1, 1)]⟩
def key2331 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, 0), (1, -1), (1, 1)]⟩
def key2332 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -2), (0, 1), (1, -1), (1, 0)]⟩
def key2334 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -1), (0, 0), (1, -2), (1, 1)]⟩
def key2335 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, -1), (0, 1), (1, -2), (1, 0)]⟩
def key2337 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 0), (1, -3), (1, 1)]⟩
def key2338 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 0)]⟩
def key2339 : Key := ⟨0, 1, [(-1, 1), (-1, 1), (0, 0), (0, 1), (1, -2), (1, -1)]⟩
def key2342 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, -1), (1, 0), (1, 0)]⟩
def key2344 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 0)]⟩
def key2348 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 0)]⟩
def key2350 : Key := ⟨0, 1, [(-1, 1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, -1)]⟩
def key2365 : Key := ⟨1, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩

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

def key259 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -1)]⟩
def key312 : Key := ⟨0, 0, [(-2, -1), (-1, -1), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key313 : Key := ⟨0, 0, [(-2, -1), (-1, -1), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key324 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key325 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key327 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 0), (1, 3), (2, -2)]⟩
def key329 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key339 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key341 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key379 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 1)]⟩
def key382 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 1), (0, 1), (1, 1), (2, 0)]⟩

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

def key414 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 1)]⟩
def key415 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, -1), (0, 1), (1, 1), (2, 0)]⟩
def key419 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (0, 1), (1, 1), (2, -1)]⟩
def key432 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 1), (2, 0)]⟩
def key464 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (2, 1)]⟩
def key466 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -3), (0, 1), (1, 1), (2, 0)]⟩
def key474 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key476 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, -1), (0, 0), (1, 1), (2, -1)]⟩
def key483 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (0, 1), (1, 1), (2, -3)]⟩

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

def key565 : Key := ⟨0, 0, [(-2, 1), (-1, -3), (0, 0), (0, 0), (1, 1), (2, 1)]⟩
def key567 : Key := ⟨0, 0, [(-2, 1), (-1, -3), (0, 0), (0, 1), (1, 1), (2, 0)]⟩
def key582 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key584 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, 0), (0, 0), (1, 1), (2, -1)]⟩
def key590 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 0), (1, 1), (2, 1)]⟩
def key592 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -3), (0, 1), (1, 1), (2, 0)]⟩
def key600 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 0)]⟩
def key602 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, -1), (0, 0), (1, 1), (2, -1)]⟩
def key609 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 1), (1, 1), (2, -3)]⟩

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

def key655 : Key := ⟨0, 0, [(-2, 2), (-1, -2), (0, -1), (0, 0), (1, 1), (2, 0)]⟩
def key708 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 1), (1, 1), (1, 1)]⟩
def key711 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩
def key717 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key719 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key720 : Key := ⟨0, 0, [(-1, -3), (-1, 1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key725 : Key := ⟨0, 0, [(-1, -2), (-1, -1), (0, 0), (0, 0), (1, 1), (1, 2)]⟩
def key727 : Key := ⟨0, 0, [(-1, -2), (-1, -1), (0, 0), (0, 2), (1, 0), (1, 1)]⟩
def key728 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, -1), (0, 0), (1, 1), (1, 2)]⟩
def key729 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 2)]⟩
def key730 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, -1), (0, 2), (1, 0), (1, 1)]⟩
def key735 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 2)]⟩
def key736 : Key := ⟨0, 0, [(-1, -2), (-1, 0), (0, 0), (0, 2), (1, -1), (1, 1)]⟩
def key739 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 0), (1, 0), (1, 2)]⟩
def key740 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 2), (1, 0), (1, 0)]⟩
def key744 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 0), (1, -1), (1, 2)]⟩
def key745 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, 0), (0, 2), (1, -1), (1, 0)]⟩
def key748 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, -1), (0, 0), (1, 0), (1, 1)]⟩
def key749 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, -1), (0, 1), (1, 0), (1, 0)]⟩
def key752 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 0), (1, -1), (1, 1)]⟩
def key753 : Key := ⟨0, 0, [(-1, -2), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0)]⟩

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

def key781 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 0), (1, 1), (1, 1)]⟩
def key784 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 0), (0, 1), (1, 0), (1, 1)]⟩
def key786 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, 1), (0, 1), (1, 0), (1, 0)]⟩
def key794 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -2), (0, 0), (1, 1), (1, 2)]⟩
def key795 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -2), (0, 1), (1, 0), (1, 2)]⟩
def key796 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -2), (0, 2), (1, 0), (1, 1)]⟩
def key806 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 0), (1, 1), (1, 1)]⟩
def key809 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 1)]⟩
def key813 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 1), (1, -2), (1, 2)]⟩
def key814 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 1)]⟩
def key815 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, 0), (0, 2), (1, -2), (1, 1)]⟩
def key816 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, 1), (0, 1), (1, -1), (1, 0)]⟩
def key819 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 0), (1, 0), (1, 2)]⟩
def key820 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -2), (0, 2), (1, 0), (1, 0)]⟩
def key822 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -1), (0, 0), (1, 0), (1, 1)]⟩
def key823 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, -1), (0, 1), (1, 0), (1, 0)]⟩
def key826 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩
def key827 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 0), (1, -1), (1, 1)]⟩
def key828 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0)]⟩
def key829 : Key := ⟨0, 0, [(-1, -1), (-1, 1), (0, 0), (0, 2), (1, -2), (1, 0)]⟩
def key832 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 0), (1, 0), (1, 1)]⟩
def key833 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -2), (0, 1), (1, 0), (1, 0)]⟩
def key841 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, 1)]⟩
def key842 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, 0), (0, 1), (1, -2), (1, 0)]⟩
def key862 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 1), (1, 1), (1, 1)]⟩
def key869 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 1), (1, -1), (1, 2)]⟩
def key870 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, 2), (1, -1), (1, 1)]⟩
def key875 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, -1), (1, 1), (1, 1)]⟩
def key878 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 1), (1, -2), (1, 2)]⟩
def key879 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 1), (1, -1), (1, 1)]⟩
def key880 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -1), (0, 2), (1, -2), (1, 1)]⟩
def key887 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 1), (0, 1), (1, -3), (1, 1)]⟩
def key894 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 0), (1, 1), (1, 1)]⟩

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

def key896 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 1)]⟩
def key903 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 0), (1, -1), (1, 2)]⟩
def key904 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, 2), (1, -1), (1, 0)]⟩
def key906 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, -1), (1, 0), (1, 1)]⟩
def key909 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, 2)]⟩
def key910 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 1)]⟩
def key911 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0)]⟩
def key912 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -1), (0, 2), (1, -2), (1, 0)]⟩
def key917 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 1)]⟩
def key918 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, -1)]⟩
def key920 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 1), (0, 1), (1, -3), (1, 0)]⟩
def key929 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 1)]⟩
def key930 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, 1), (1, -1), (1, 0)]⟩
def key936 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 1)]⟩
def key937 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -1), (0, 1), (1, -2), (1, 0)]⟩
def key949 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 0), (1, 0), (1, 1)]⟩
def key950 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -3), (0, 1), (1, 0), (1, 0)]⟩
def key952 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -1), (0, -1), (1, 0), (1, 0)]⟩
def key953 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0)]⟩
def key956 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (1, -3), (1, 1)]⟩
def key957 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 0), (1, -1), (1, -1)]⟩
def key958 : Key := ⟨0, 0, [(-1, 1), (-1, 1), (0, 0), (0, 1), (1, -3), (1, 0)]⟩
def key982 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key986 : Key := ⟨0, 1, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key988 : Key := ⟨0, 1, [(-3, -3), (0, 1), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key1003 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key1004 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key1007 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key1008 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key1009 : Key := ⟨0, 1, [(-3, -2), (0, -1), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key1017 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key1020 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key1021 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key1022 : Key := ⟨0, 1, [(-3, -2), (0, 0), (0, 2), (1, -1), (1, 0), (1, 1)]⟩
def key1023 : Key := ⟨0, 1, [(-3, -2), (0, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩

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

def key1038 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (1, 0), (1, 1), (1, 2)]⟩
def key1039 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key1042 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key1043 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key1044 : Key := ⟨0, 1, [(-3, -1), (0, -2), (0, 2), (1, 0), (1, 0), (1, 1)]⟩
def key1073 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key1077 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key1078 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key1080 : Key := ⟨0, 1, [(-3, -1), (0, 0), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key1081 : Key := ⟨0, 1, [(-3, -1), (0, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key1096 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 0), (1, 1), (1, 1), (1, 1)]⟩
def key1100 : Key := ⟨0, 1, [(-3, 0), (0, -3), (0, 1), (1, 0), (1, 1), (1, 1)]⟩
def key1116 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (1, 0), (1, 1), (1, 2)]⟩
def key1117 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, -1), (1, 1), (1, 1), (1, 1)]⟩
def key1125 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key1128 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 0), (1, 2)]⟩
def key1129 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 1), (1, -1), (1, 1), (1, 1)]⟩
def key1130 : Key := ⟨0, 1, [(-3, 0), (0, -2), (0, 2), (1, -1), (1, 0), (1, 1)]⟩

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

def key1152 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key1156 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 0), (1, 2)]⟩
def key1157 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 1), (1, -2), (1, 1), (1, 1)]⟩
def key1159 : Key := ⟨0, 1, [(-3, 0), (0, -1), (0, 2), (1, -2), (1, 0), (1, 1)]⟩
def key1171 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 1), (1, -3), (1, 1), (1, 1)]⟩
def key1174 : Key := ⟨0, 1, [(-3, 0), (0, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩
def key1175 : Key := ⟨0, 1, [(-3, 0), (0, 1), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key1176 : Key := ⟨0, 1, [(-3, 0), (0, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key1185 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 1), (1, 1)]⟩
def key1186 : Key := ⟨0, 1, [(-3, 1), (0, -3), (0, 1), (1, 0), (1, 0), (1, 1)]⟩
def key1195 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 1), (1, 1)]⟩
def key1201 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 1), (1, 1)]⟩
def key1202 : Key := ⟨0, 1, [(-3, 1), (0, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key1214 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 1), (1, 1)]⟩
def key1216 : Key := ⟨0, 1, [(-3, 1), (0, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key1222 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 1), (1, 1)]⟩
def key1224 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1)]⟩
def key1225 : Key := ⟨0, 1, [(-3, 1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key1233 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, -1), (1, 0), (1, 0), (1, 1)]⟩
def key1236 : Key := ⟨0, 1, [(-3, 2), (0, -2), (0, 0), (1, -1), (1, 0), (1, 1)]⟩
def key1243 : Key := ⟨0, 1, [(-3, 2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1)]⟩
def key1247 : Key := ⟨0, 1, [(-3, 2), (0, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2608, 64), (key2614, -64), (key2624, -64), (key2630, 96), (key2638, -52), (key2657, -12), (key2659, 32), (key2663, -64), (key2669, 64), (key2698, 84), (key2704, -144), (key2724, 60), (key2752, 56), (key2757, -60), (key2778, 44), (key2784, -48), (key2792, 8), (key2801, -64), (key2807, 96), (key2827, -52), (key2919, -32), (key2922, 32), (key3007, 4), (key3009, -4), (key3011, -12), (key3016, 32), (key3022, 32), (key3025, -32)]

def entry2_0 : Integer.Sparse Key := [(key2609, 64), (key2613, -64), (key2625, -64), (key2629, 96), (key2637, -32), (key2647, -32), (key2652, 32), (key2664, -64), (key2668, 64), (key2699, 64), (key2703, -96), (key2723, 32), (key2736, 32), (key2746, -32), (key2779, 64), (key2783, -96), (key2791, 32), (key2802, -64), (key2806, 96), (key2826, -32), (key2896, -32), (key2903, 32), (key2937, 32), (key2942, -32), (key2949, -32), (key2959, 32), (key2975, 32), (key2982, -32)]

def entry2_1 : Integer.Sparse Key := [(key1292, 64), (key1297, -64), (key1312, -64), (key1317, 96), (key1325, -32), (key1338, -32), (key1344, 32), (key1387, -64), (key1392, 64), (key1420, 64), (key1425, -96), (key1443, 32), (key1456, 32), (key1465, -32), (key1542, 64), (key1547, -96), (key1555, 32), (key1569, -64), (key1574, 96), (key1592, -32), (key1658, -32), (key1666, 32), (key1773, 32), (key1779, -32), (key1789, -32), (key1797, 32), (key1816, 32), (key1824, -32)]

def entry2_2 : Integer.Sparse Key := [(key2608, 64), (key2611, -64), (key2624, -64), (key2627, 96), (key2636, -52), (key2645, -12), (key2651, 32), (key2663, -64), (key2666, 64), (key2698, 84), (key2701, -144), (key2722, 60), (key2734, 56), (key2745, -60), (key2778, 44), (key2781, -48), (key2790, 8), (key2801, -64), (key2804, 96), (key2825, -52), (key2895, -32), (key2902, 32), (key2935, 4), (key2941, -4), (key2947, -12), (key2958, 32), (key2974, 32), (key2981, -32)]

def entry3_0 : Integer.Sparse Key := [(key1003, 96), (key1009, -96), (key1017, -96), (key1022, 96), (key1038, -96), (key1044, 96), (key1073, 96), (key1080, -96), (key1125, 96), (key1130, -96), (key1152, -96), (key1159, 96)]

def entry3_1 : Integer.Sparse Key := [(key25, 48), (key27, -48), (key37, -64), (key40, 60), (key50, -48), (key52, 48), (key76, 64), (key81, -60), (key117, 36), (key120, -48), (key139, -36), (key144, 48), (key197, 6), (key201, -6), (key210, 48), (key213, -48), (key215, -32), (key217, 36), (key379, -48), (key382, 48), (key464, 60), (key466, -48), (key483, -6), (key565, 32), (key567, -36), (key590, -60), (key592, 48), (key609, 6)]

def entry3_2 : Integer.Sparse Key := [(key1003, 96), (key1007, -96), (key1017, -96), (key1020, 96), (key1038, -96), (key1042, 96), (key1073, 96), (key1077, -96), (key1125, 96), (key1128, -96), (key1152, -96), (key1156, 96)]

def entry3_3 : Integer.Sparse Key := [(key10, 96), (key13, -192), (key15, 96), (key93, -96), (key96, 96), (key158, 124), (key163, -144), (key169, 68), (key170, -48), (key189, -96), (key192, 96)]

def entry4_0 : Integer.Sparse Key := [(key2378, 48), (key2383, -48), (key2390, -64), (key2394, 60), (key2406, -48), (key2411, 48), (key2437, 64), (key2443, -60), (key2480, 36), (key2484, -48), (key2503, -36), (key2509, 48), (key2571, 6), (key2576, -6), (key2587, 48), (key2593, -48), (key2598, -32), (key2600, 36), (key2766, -48), (key2772, 48), (key2887, 60), (key2889, -48), (key2910, -6), (key2929, 32), (key2931, -36), (key2966, -60), (key2968, 48), (key2989, 6)]

def entry4_1 : Integer.Sparse Key := [(key1256, 96), (key1261, -96), (key1265, -96), (key1268, 96), (key1531, -96), (key1536, 96), (key1648, 96), (key1651, -96), (key1765, 96), (key1768, -96), (key1806, -96), (key1809, 96)]

def entry4_2 : Integer.Sparse Key := [(key2378, 96), (key2381, -96), (key2390, -96), (key2392, 96), (key2406, -96), (key2409, 96), (key2437, 96), (key2440, -96), (key2480, 96), (key2482, -96), (key2503, -96), (key2506, 96)]

def entry4_3 : Integer.Sparse Key := [(key982, 96), (key986, -192), (key988, 96), (key1096, -96), (key1100, 96), (key1171, 96), (key1175, -96), (key1185, 96), (key1186, -96), (key1222, -96), (key1224, 96)]

def entry4_4 : Integer.Sparse Key := [(key2362, 96), (key2365, -192), (key2367, 96), (key2457, -96), (key2460, 96), (key2521, 124), (key2525, -144), (key2532, 68), (key2533, -48), (key2562, -96), (key2564, 96)]

def entry5_0 : Integer.Sparse Key := [(key2612, -20), (key2616, -12), (key2618, 22), (key2621, 10), (key2628, 32), (key2640, 6), (key2641, -32), (key2644, -24), (key2646, -6), (key2648, -8), (key2653, 22), (key2660, 10), (key2667, 32), (key2673, -32), (key2702, 64), (key2726, -6), (key2728, -64), (key2732, 24), (key2735, -84), (key2737, 32), (key2747, 58), (key2758, -12), (key2782, -32), (key2794, -12), (key2795, 32), (key2805, -52), (key2809, -12), (key2829, 52), (key2831, 58), (key2835, -12), (key2860, 24), (key2870, -24), (key2893, 72), (key2897, -32), (key2904, -40), (key2936, 6), (key2938, 8), (key2943, -20), (key2948, 44), (key2950, -20), (key2960, -44), (key2972, -72), (key2976, 32), (key2983, 40), (key3010, 6), (key3012, 6), (key3017, -20), (key3023, -24), (key3026, 24)]

def entry5_2 : Integer.Sparse Key := [(key2616, -32), (key2619, 32), (key2632, 32), (key2642, -32), (key2649, -32), (key2654, 32), (key2671, 32), (key2674, -32), (key2706, -32), (key2729, 32), (key2738, 32), (key2748, -32), (key2786, 64), (key2794, -96), (key2796, 32), (key2809, -64), (key2829, 96), (key2832, -32), (key2860, 96), (key2870, -96), (key2898, -32), (key2905, 32), (key2939, -64), (key2944, 64), (key2951, 64), (key2961, -64), (key2977, -64), (key2984, 64)]

def entry5_3 : Integer.Sparse Key := [(key1039, 96), (key1043, -96), (key1078, -96), (key1081, 96), (key1117, -96), (key1129, 96), (key1157, 96), (key1176, -96), (key1195, 96), (key1201, -96), (key1216, -96), (key1225, 96)]

def entry5_4 : Integer.Sparse Key := [(key2379, 12), (key2382, -12), (key2393, -8), (key2407, 72), (key2410, -72), (key2441, -78), (key2445, 72), (key2473, -58), (key2483, 72), (key2507, 60), (key2526, -72), (key2539, 42), (key2544, -50), (key2555, -8), (key2557, -24), (key2565, 48), (key2592, -12), (key2595, 12), (key2602, 8), (key2771, 24), (key2774, -24), (key2848, -38), (key2882, 54), (key2891, 24), (key2912, -46), (key2933, -18), (key2934, 24), (key2970, 36), (key2991, 8), (key2993, -72), (key2996, -24), (key3003, 48)]

def entry5_5 : Integer.Sparse Key := [(key2617, 64), (key2620, -64), (key2633, -64), (key2643, 84), (key2650, 44), (key2655, -64), (key2672, 32), (key2675, -32), (key2707, -60), (key2730, 60), (key2739, 32), (key2749, -36), (key2787, -4), (key2797, 32), (key2810, 32), (key2833, -36), (key2899, -32), (key2906, 8), (key2940, 4), (key2945, -28), (key2952, -28), (key2962, -64), (key2964, 96), (key2978, 56), (key2985, 64), (key2994, -144), (key3001, -48), (key3004, 96)]

def entry6_3 : Integer.Sparse Key := [(key25, 96), (key26, -96), (key37, -96), (key39, 96), (key50, -96), (key51, 96), (key76, 96), (key79, -96), (key117, 96), (key119, -96), (key139, -96), (key142, 96)]

def entry6_6 : Integer.Sparse Key := [(key236, 64), (key239, -64), (key248, -64), (key251, 96), (key260, -52), (key267, -12), (key271, 32), (key302, -64), (key305, 64), (key316, 84), (key319, -144), (key328, 60), (key335, 56), (key340, -60), (key385, 44), (key388, -48), (key397, 8), (key406, -64), (key409, 96), (key418, -52), (key469, -32), (key475, 32), (key568, 4), (key572, -4), (key578, -12), (key583, 32), (key595, 32), (key601, -32)]

def entry7_0 : Integer.Sparse Key := [(key2608, 32), (key2614, -32), (key2624, -32), (key2638, 44), (key2657, 20), (key2659, -32), (key2663, -32), (key2669, 32), (key2698, 44), (key2704, -120), (key2724, 60), (key2752, 64), (key2757, -56), (key2778, 20), (key2784, 24), (key2792, -32), (key2801, -32), (key2807, 96), (key2827, -96), (key2858, -24), (key2868, 24), (key2918, -72), (key2919, 32), (key2922, 40), (key3007, -28), (key3009, 24), (key3011, -32), (key3016, 64), (key3021, 72), (key3022, -8), (key3025, -64)]

def entry7_1 : Integer.Sparse Key := [(key1291, 32), (key1299, -32), (key1311, -32), (key1327, 32), (key1352, 32), (key1355, -32), (key1386, -32), (key1394, 32), (key1419, 32), (key1427, -96), (key1445, 64), (key1473, 64), (key1481, -64), (key1541, 32), (key1557, -32), (key1568, -32), (key1576, 96), (key1594, -64), (key1682, -96), (key1684, 32), (key1690, 64), (key1897, -32), (key1900, 32), (key1904, -64), (key1912, 64), (key1919, 96), (key1921, -32), (key1927, -64)]

def entry7_2 : Integer.Sparse Key := [(key2609, 32), (key2613, -32), (key2625, -32), (key2637, 32), (key2647, 32), (key2652, -32), (key2664, -32), (key2668, 32), (key2699, 32), (key2723, -32), (key2736, -32), (key2746, 32), (key2779, 32), (key2783, -96), (key2791, 64), (key2802, -32), (key2806, 96), (key2826, -64), (key2857, -96), (key2867, 96), (key2896, 32), (key2903, -32), (key2937, 64), (key2942, -64), (key2949, -64), (key2959, 64), (key2975, 64), (key2982, -64)]

def entry7_3 : Integer.Sparse Key := [(key1038, -96), (key1044, 96), (key1073, 96), (key1080, -96), (key1116, 96), (key1130, -96), (key1152, -96), (key1174, 96), (key1233, -96), (key1236, 96), (key1243, 96), (key1247, -96)]

def entry7_4 : Integer.Sparse Key := [(key2378, -36), (key2383, 24), (key2390, 26), (key2394, -12), (key2406, -84), (key2411, 72), (key2437, 90), (key2443, -72), (key2472, 96), (key2480, -24), (key2484, -72), (key2503, -60), (key2509, -24), (key2524, 84), (key2569, -48), (key2571, 54), (key2576, 48), (key2580, -58), (key2587, 36), (key2593, -24), (key2598, -26), (key2600, 12), (key2766, -12), (key2772, 24), (key2880, -48), (key2887, 24), (key2889, -24), (key2910, 42), (key2929, 6), (key2931, -24), (key2966, -36), (key2968, 24), (key2989, 48), (key2995, 12), (key3002, -38)]

def entry7_5 : Integer.Sparse Key := [(key2612, -16), (key2616, -48), (key2618, 30), (key2621, 34), (key2628, 16), (key2632, 48), (key2640, -2), (key2641, -40), (key2644, -48), (key2646, 2), (key2648, -16), (key2653, 30), (key2658, -24), (key2660, 34), (key2667, 4), (key2671, -36), (key2673, 8), (key2676, 24), (key2702, 32), (key2706, 48), (key2726, -6), (key2728, -32), (key2732, -24), (key2735, -24), (key2737, -8), (key2747, 26), (key2753, -24), (key2758, 24), (key2782, -16), (key2794, 24), (key2795, -8), (key2798, -24), (key2805, -20), (key2809, -12), (key2829, 74), (key2831, 26), (key2835, -36), (key2860, -24), (key2870, -48), (key2885, 72), (key2893, 24), (key2897, 8), (key2904, -8), (key2920, 24), (key2923, 24), (key2927, -60), (key2936, 6), (key2938, -8), (key2943, 8), (key2948, 22), (key2950, -28), (key2960, -22), (key2972, -48), (key2976, 40), (key2983, 32), (key2997, 24), (key2998, -36), (key3000, -12), (key3010, 6), (key3012, 6), (key3017, -10), (key3023, -24), (key3030, 12)]

def entry7_7 : Integer.Sparse Key := [(key2608, 64), (key2614, -64), (key2624, -64), (key2638, 88), (key2657, 40), (key2659, -64), (key2663, 32), (key2669, -32), (key2698, -36), (key2704, -48), (key2724, 72), (key2752, 56), (key2757, -60), (key2778, -28), (key2784, 48), (key2792, 8), (key2801, -64), (key2807, 96), (key2827, -52), (key2851, 96), (key2858, -96), (key2868, -48), (key2918, -96), (key2919, 64), (key2922, 56), (key3007, -8), (key3009, -4), (key3011, -12), (key3016, 32), (key3021, 48), (key3022, 8), (key3025, -32)]

def entry8_0 : Integer.Sparse Key := [(key2612, 20), (key2616, 12), (key2618, -22), (key2621, -10), (key2628, 52), (key2632, 12), (key2640, -52), (key2641, -58), (key2644, 12), (key2646, -44), (key2648, 20), (key2653, 44), (key2658, -6), (key2660, 20), (key2667, -8), (key2671, -24), (key2673, 8), (key2676, 24), (key2702, 32), (key2706, -24), (key2726, 66), (key2728, -32), (key2732, -24), (key2735, -12), (key2737, -8), (key2747, 26), (key2753, 24), (key2758, -36), (key2782, -40), (key2794, 12), (key2795, 40), (key2798, -24), (key2805, -32), (key2829, -6), (key2831, 32), (key2835, 24), (key2860, 24), (key2870, -24), (key2893, 72), (key2897, -40), (key2904, -32), (key2920, -24), (key2923, 24), (key2936, 30), (key2938, -8), (key2943, -28), (key2948, 6), (key2950, 8), (key2960, -22), (key2972, -72), (key2976, 40), (key2983, 32), (key3010, 6), (key3017, -10)]

def entry8_2 : Integer.Sparse Key := [(key2616, 32), (key2619, -32), (key2632, 64), (key2640, -96), (key2642, 32), (key2649, -64), (key2654, 64), (key2671, -32), (key2674, 32), (key2706, -64), (key2726, 96), (key2729, -32), (key2738, 64), (key2748, -64), (key2786, 32), (key2796, -32), (key2809, -32), (key2832, 32), (key2860, 96), (key2870, -96), (key2898, -64), (key2905, 64), (key2939, -32), (key2944, 32), (key2951, 32), (key2961, -32), (key2977, -32), (key2984, 32)]

def entry8_3 : Integer.Sparse Key := [(key1004, 96), (key1008, -96), (key1021, -96), (key1023, 96), (key1117, -96), (key1129, 96), (key1157, 96), (key1176, -96), (key1195, 96), (key1202, -96), (key1214, -96), (key1225, 96)]

def entry8_4 : Integer.Sparse Key := [(key2379, 72), (key2382, -72), (key2393, -78), (key2395, 72), (key2407, 12), (key2410, -12), (key2441, -8), (key2473, -58), (key2483, 60), (key2507, 72), (key2526, -72), (key2539, 42), (key2544, -8), (key2545, -24), (key2555, -50), (key2565, 48), (key2592, 24), (key2595, -24), (key2602, -18), (key2603, 24), (key2771, -12), (key2774, 12), (key2848, -38), (key2882, 54), (key2891, 36), (key2912, 8), (key2914, -72), (key2933, 8), (key2970, 24), (key2991, -46), (key2996, -24), (key3003, 48)]

def entry8_7 : Integer.Sparse Key := [(key2612, 4), (key2616, -36), (key2618, 8), (key2621, 24), (key2628, 32), (key2640, 22), (key2641, -32), (key2644, -24), (key2646, -22), (key2648, -8), (key2653, 22), (key2660, 10), (key2667, -4), (key2671, -60), (key2673, 16), (key2676, 48), (key2702, 16), (key2706, -24), (key2726, 90), (key2728, -40), (key2732, -48), (key2737, -16), (key2747, 34), (key2753, 24), (key2758, -24), (key2782, -8), (key2786, 48), (key2795, 8), (key2798, -48), (key2805, -16), (key2809, 48), (key2829, -8), (key2831, -8), (key2835, -24), (key2860, -24), (key2870, -48), (key2885, 72), (key2893, 24), (key2897, -8), (key2904, 8), (key2920, -24), (key2927, 12), (key2936, 6), (key2938, -16), (key2943, -8), (key2948, 8), (key2950, -8), (key2960, 8), (key2972, -48), (key2976, 32), (key2983, 40), (key2997, 24), (key2998, -12), (key3000, -36), (key3008, -24), (key3010, 30), (key3012, -24), (key3017, 24), (key3023, 24), (key3026, 24), (key3030, -60)]

def entry9_0 : Integer.Sparse Key := [(key2066, -96), (key2071, 96), (key2093, 96), (key2096, -96), (key2155, 96), (key2168, -96), (key2195, -96), (key2201, 96), (key2248, -96), (key2255, 96), (key2306, 96), (key2311, -96)]

def entry9_1 : Integer.Sparse Key := [(key312, -12), (key313, 12), (key324, 12), (key325, -120), (key329, 102), (key339, 84), (key341, -90), (key414, 8), (key415, 96), (key419, -102), (key474, -72), (key476, 72), (key582, -58), (key584, 72), (key600, 72), (key602, -72), (key725, 12), (key727, -12), (key728, -12), (key730, 24), (key736, 12), (key748, -6), (key752, -6), (key794, -8), (key815, -38), (key832, 6), (key841, 24), (key870, -24), (key880, 24), (key929, 24), (key936, -24)]

def entry9_2 : Integer.Sparse Key := [(key2064, -96), (key2070, 96), (key2080, 96), (key2086, -96), (key2153, 96), (key2167, -96), (key2177, -96), (key2188, 96), (key2247, -96), (key2254, 96), (key2280, 96), (key2288, -96)]

def entry9_3 : Integer.Sparse Key := [(key66, -70), (key67, 96), (key78, 84), (key80, -84), (key131, 60), (key141, -58), (key143, -96), (key160, 84), (key178, -48), (key183, 102), (key191, -58), (key708, -26), (key717, 12), (key719, -12), (key862, 36), (key887, -48), (key894, -38), (key917, 90), (key949, 12), (key956, -38)]

def entry9_4 : Integer.Sparse Key := [(key1992, -96), (key1995, 96), (key2002, 96), (key2004, -96), (key2237, 96), (key2260, -96), (key2271, -96), (key2273, -96), (key2295, 192), (key2325, 96), (key2337, -96)]

def entry9_5 : Integer.Sparse Key := [(key2035, -96), (key2038, 96), (key2065, 96), (key2073, -96), (key2083, -96), (key2088, 96), (key2178, 96), (key2180, -96), (key2278, -96), (key2282, 96), (key2329, 96), (key2331, -96)]

def entry9_6 : Integer.Sparse Key := [(key729, -96), (key735, 96), (key739, 96), (key744, -96), (key795, 96), (key813, -96), (key819, -96), (key826, 96), (key869, -96), (key878, 96), (key903, 96), (key909, -96)]

def entry9_7 : Integer.Sparse Key := [(key2031, 96), (key2036, -96), (key2061, -96), (key2071, 96), (key2093, 96), (key2096, -96), (key2150, -96), (key2155, 96), (key2243, 96), (key2248, -96), (key2304, -96), (key2306, 96)]

def entry9_8 : Integer.Sparse Key := [(key2035, -96), (key2038, 96), (key2081, 96), (key2083, -96), (key2154, 96), (key2170, -96), (key2180, -96), (key2190, 96), (key2278, -96), (key2290, 96), (key2329, 96), (key2334, -96)]

def entry9_9 : Integer.Sparse Key := [(key781, 96), (key784, -96), (key806, -192), (key809, 96), (key814, 124), (key822, 68), (key827, -96), (key875, 96), (key879, -144), (key906, -48), (key910, 96)]

def entry10_0 : Integer.Sparse Key := [(key2080, 96), (key2084, -96), (key2086, -96), (key2089, 96), (key2177, -96), (key2181, 96), (key2188, 96), (key2191, -96), (key2280, 96), (key2283, -96), (key2288, -96), (key2291, 96)]

def entry10_1 : Integer.Sparse Key := [(key739, 96), (key740, -96), (key744, -96), (key745, 96), (key819, -96), (key820, 96), (key826, 96), (key829, -96), (key903, 96), (key904, -96), (key909, -96), (key912, 96)]

def entry10_2 : Integer.Sparse Key := [(key2093, 96), (key2094, -96), (key2096, -96), (key2097, 96), (key2195, -96), (key2196, 96), (key2201, 96), (key2202, -96), (key2306, 96), (key2307, -96), (key2311, -96), (key2312, 96)]

def entry10_3 : Integer.Sparse Key := [(key717, 96), (key719, -192), (key720, 96), (key894, -96), (key896, 96), (key917, 96), (key920, -96), (key949, 96), (key950, -96), (key956, -96), (key958, 96)]

def entry10_4 : Integer.Sparse Key := [(key2002, 96), (key2004, -192), (key2005, 96), (key2271, -96), (key2273, 96), (key2295, 96), (key2297, -96), (key2325, 96), (key2326, -96), (key2337, -96), (key2338, 96)]

def entry10_5 : Integer.Sparse Key := [(key2178, 96), (key2180, -96), (key2190, -96), (key2192, 96), (key2278, -96), (key2282, 96), (key2290, 96), (key2298, -96), (key2329, 96), (key2331, -96), (key2335, -96), (key2339, 96)]

def entry10_6 : Integer.Sparse Key := [(key748, 96), (key749, -96), (key752, -96), (key753, 96), (key832, -96), (key833, 96), (key841, 96), (key842, -96), (key929, 96), (key930, -96), (key936, -96), (key937, 96)]

def entry10_7 : Integer.Sparse Key := [(key2177, -96), (key2181, 96), (key2188, 96), (key2191, -96), (key2277, 96), (key2283, -96), (key2288, -96), (key2296, 96), (key2342, -96), (key2344, 96), (key2348, 96), (key2350, -96)]

def entry10_8 : Integer.Sparse Key := [(key2081, 96), (key2083, -96), (key2088, -96), (key2090, 96), (key2278, -96), (key2282, 96), (key2290, 96), (key2298, -96), (key2329, 96), (key2332, -96), (key2334, -96), (key2339, 96)]

def entry10_9 : Integer.Sparse Key := [(key822, -96), (key823, 96), (key827, 96), (key828, -96), (key906, 96), (key910, -96), (key911, -96), (key918, 96), (key952, -96), (key953, 192), (key957, -96)]

def entry10_10 : Integer.Sparse Key := [(key781, 96), (key784, -192), (key786, 96), (key806, -96), (key809, 96), (key814, 124), (key816, -144), (key822, 68), (key823, -48), (key827, -96), (key828, 96)]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row688 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

def row689 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

def row690 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

def row691 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row692 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row693 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row694 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row695 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row696 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row697 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

def row698 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

def row699 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row706 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row707 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row708 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row709 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row710 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row711 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row748 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

def row749 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

def row750 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

def row751 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row752 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row753 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row754 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row755 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row756 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row757 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

def row758 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

def row759 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

def row766 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row767 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row768 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row769 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row770 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row771 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row778 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row779 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row780 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row781 : Integer.Sparse Key := [(key1033, 6), (key1041, -6), (key1111, -6), (key1127, 6), (key1193, 6), (key1199, -6)]

def row782 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row783 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row784 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row785 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row786 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row787 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row788 : Integer.Sparse Key := [(key1033, -6), (key1041, 6), (key1111, 6), (key1127, -6), (key1193, -6), (key1199, 6)]

def row789 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row790 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row791 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row792 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row793 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row794 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row795 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, -6), (key70, 6), (key111, 6), (key133, -6)]

def row796 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row797 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row798 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row799 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row800 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row801 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row802 : Integer.Sparse Key := [(key20, -6), (key31, 6), (key45, 6), (key70, -6), (key111, -6), (key133, 6)]

def row803 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row804 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row805 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row806 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row807 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row808 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row809 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, -6), (key1071, 6), (key1123, 6), (key1150, -6)]

def row810 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row811 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row812 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row813 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row814 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row815 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row816 : Integer.Sparse Key := [(key1001, -6), (key1015, 6), (key1036, 6), (key1071, -6), (key1123, -6), (key1150, 6)]

def row817 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row818 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row819 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row820 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

def row821 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

def row822 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

def row823 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key151, 6), (key193, 6), (key202, -6)]

def row824 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

def row825 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

def row826 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

def row827 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

def row828 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

def row829 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

def row830 : Integer.Sparse Key := [(key1, -6), (key7, 6), (key84, 6), (key151, -6), (key193, -6), (key202, 6)]

def row831 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row832 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

def row833 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

def row834 : Integer.Sparse Key := [(key2785, -6), (key2793, 6), (key2808, 6), (key2828, -6), (key2859, -6), (key2869, 6)]

def row835 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row836 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row837 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row838 : Integer.Sparse Key := [(key2785, 6), (key2793, -6), (key2808, -6), (key2828, 6), (key2859, 6), (key2869, -6)]

def row839 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row840 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row841 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row842 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row843 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row844 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row845 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row846 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row847 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row848 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1382, 6), (key1415, -6), (key1537, -6), (key1564, 6)]

def row849 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row850 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row851 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row852 : Integer.Sparse Key := [(key1287, 6), (key1307, -6), (key1382, -6), (key1415, 6), (key1537, 6), (key1564, -6)]

def row853 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row854 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row855 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row856 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row857 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row858 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row859 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row860 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row861 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row862 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2665, 6), (key2700, -6), (key2780, -6), (key2803, 6)]

def row863 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row864 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row865 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row866 : Integer.Sparse Key := [(key2610, 6), (key2626, -6), (key2665, -6), (key2700, 6), (key2780, 6), (key2803, -6)]

def row867 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row868 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row869 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row870 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row871 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row872 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row873 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row874 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row875 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row876 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, 6), (key1067, -6), (key1119, -6), (key1146, 6)]

def row877 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row878 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row879 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row880 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, -6), (key1067, 6), (key1119, 6), (key1146, -6)]

def row881 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row882 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row883 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row884 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row885 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row886 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row887 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row888 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row889 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row890 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2661, 6), (key2696, -6), (key2776, -6), (key2799, 6)]

def row891 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row892 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row893 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row894 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, -6), (key2696, 12), (key2799, -6)]

def row895 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row896 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

def row897 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

def row898 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

def row899 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

def row900 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

def row901 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row902 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row903 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row910 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

def row911 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

def row912 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

def row925 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

def row926 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

def row927 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row970 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

def row971 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

def row972 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

def row985 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row986 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row987 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1018 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2), (key426, 2)]

def row1019 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2), (key426, 2)]

def row1020 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2), (key426, 2)]

def row1021 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2), (key426, 2)]

def row1022 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -4), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2)]

def row1023 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -4), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1524 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

def row1525 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

def row1526 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

def row1527 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1528 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1529 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1530 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1531 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1532 : Integer.Sparse Key := [(key2612, 1), (key2618, 1), (key2628, 1), (key2641, 1), (key2646, -2), (key2648, -1), (key2653, -1), (key2671, -1), (key2676, -1), (key2706, -1), (key2726, 2), (key2732, 1), (key2753, -1), (key2758, 1), (key2794, 1), (key2798, 1), (key2829, -1), (key2835, -1), (key2860, 1), (key2870, -1), (key2920, 1), (key2923, -1)]

def row1533 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -2), (key2641, 2), (key2660, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

def row1534 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -1), (key2641, 2), (key2646, -1), (key2653, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

def row1535 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -1), (key2641, 2), (key2646, -1), (key2653, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1536 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1537 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1538 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1539 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1540 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1541 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

def row1542 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1543 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1544 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1545 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1546 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1547 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

def row1548 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1549 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1550 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1551 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1552 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

def row1553 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4854 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

def row4855 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

def row4856 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

def row4857 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

def row4858 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

def row4859 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

def row4860 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -2), (key2831, 2), (key2860, -2), (key2870, 2), (key3017, -2), (key3023, -2), (key3026, 2)]

def row4861 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, 2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, 2)]

def row4862 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, 2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, 2)]

def row4863 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 2), (key2831, -2), (key2893, 2), (key2904, 2), (key2972, -2), (key2983, -2), (key3017, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4864 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 1), (key2831, -2), (key2893, 2), (key2904, 2), (key2948, 1), (key2960, 2), (key2972, -2), (key2983, -2)]

def row4865 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 1), (key2831, -2), (key2893, 2), (key2904, 2), (key2948, 1), (key2960, 2), (key2972, -2), (key2983, -2)]

def row4872 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

def row4873 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

def row4874 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

def row4875 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

def row4876 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

def row4877 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

def row4884 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

def row4885 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

def row4886 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

def row4887 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

def row4888 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

def row4889 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

def row4896 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

def row4897 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

def row4898 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

def row4899 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

def row4900 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

def row4901 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

def row4902 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

def row4903 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

def row4904 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

def row4905 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

def row4906 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

def row4907 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5099 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

def row5100 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

def row5101 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

def row5102 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

def row5103 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

def row5104 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

def row5105 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

def row5106 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

def row5107 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

def row5108 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

def row5109 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

def row5110 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

def row5111 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

def row5113 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

def row5114 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

def row5115 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

def row5116 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

def row5117 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

def row5118 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

def row5119 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5120 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

def row5121 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

def row5122 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

def row5123 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

def row5124 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

def row5125 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

def row5126 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

def row5127 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

def row5128 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

def row5129 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

def row5130 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

def row5131 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

def row5132 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

def row5133 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

def row5134 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

def row5135 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

def row5136 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

def row5137 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

def row5138 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

def row5139 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

def row5140 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

def row5141 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

def row5142 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

def row5143 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

def row5144 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

def row5145 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

def row5146 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

def row5147 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

def row5148 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5149 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5150 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5151 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5152 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5153 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5154 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5155 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5156 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5157 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2663, -2), (key2669, 2), (key2698, 2), (key2704, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, 2), (key2784, -2), (key2801, -2), (key2807, 2), (key2858, 2), (key2868, -2), (key2919, -2), (key2922, 2)]

def row5158 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5159 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, 1), (key2801, 1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, 1), (key2922, -1)]

def row5160 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5161 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5162 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2858, 2), (key2868, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5163 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5164 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5165 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2858, 2), (key2868, -2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5166 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2858, 2), (key2868, -2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5167 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5168 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2858, -1), (key2868, 1), (key3011, 1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5169 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2630, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2704, 6), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2858, 2), (key2868, -2), (key3011, 2), (key3016, -2), (key3022, -2), (key3025, 2)]

def row5170 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5171 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2704, -3), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, 1), (key3022, 1), (key3025, -1)]

def row5172 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -2), (key2704, 1), (key2757, 1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3011, 1), (key3021, 1), (key3022, -1)]

def row5173 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -2), (key2704, 1), (key2757, 1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3011, 1), (key3021, 1), (key3022, -1)]

def row5174 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3009, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5175 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3009, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5176 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2638, 1), (key2657, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 2), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5177 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2638, 1), (key2657, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 2), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5178 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5179 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5180 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5181 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2724, -1), (key2757, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3021, 1), (key3022, -1)]

def row5182 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5183 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2918, -1), (key2922, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5184 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2918, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5185 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2630, 1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 2), (key2784, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2918, -1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row5186 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3009, 1), (key3021, 1), (key3022, -1)]

def row5187 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2704, 1), (key2778, -1), (key2784, 2), (key2792, -1), (key2801, 1), (key2807, -1), (key2918, -1), (key2919, 1), (key3007, -1), (key3009, 1), (key3021, 1), (key3022, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7018 : Integer.Sparse Key := [(key2080, -4), (key2084, 4), (key2086, 4), (key2089, -4), (key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2280, -4), (key2283, 4), (key2288, 4), (key2291, -4)]

def row7019 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7020 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7021 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7022 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7023 : Integer.Sparse Key := [(key2080, -4), (key2084, 4), (key2086, 4), (key2089, -4), (key2177, 4), (key2181, -4), (key2188, -4), (key2191, 4), (key2280, -4), (key2283, 4), (key2288, 4), (key2291, -4)]

def row7024 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7025 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7026 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7027 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7028 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7029 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7030 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7031 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7032 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7033 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7034 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7035 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7036 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7037 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7038 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7039 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7040 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7041 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7042 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7043 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7044 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7045 : Integer.Sparse Key := [(key2080, 2), (key2084, -2), (key2086, -2), (key2089, 2), (key2177, -2), (key2181, 2), (key2188, 2), (key2191, -2), (key2280, 2), (key2283, -2), (key2288, -2), (key2291, 2)]

def row7046 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7047 : Integer.Sparse Key := [(key2080, -1), (key2084, 1), (key2086, 1), (key2089, -1), (key2177, 1), (key2181, -1), (key2188, -1), (key2191, 1), (key2280, -1), (key2283, 1), (key2288, 1), (key2291, -1)]

def row7048 : Integer.Sparse Key := [(key739, -4), (key740, 4), (key744, 4), (key745, -4), (key819, 4), (key820, -4), (key826, -4), (key829, 4), (key903, -4), (key904, 4), (key909, 4), (key912, -4)]

def row7049 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7050 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7051 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7052 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7053 : Integer.Sparse Key := [(key739, -4), (key740, 4), (key744, 4), (key745, -4), (key819, 4), (key820, -4), (key826, -4), (key829, 4), (key903, -4), (key904, 4), (key909, 4), (key912, -4)]

def row7054 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7055 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7056 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7057 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7058 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7059 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7060 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7061 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7062 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7063 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7064 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7065 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7066 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7067 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7068 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7069 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7070 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7071 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7072 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7073 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7074 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7075 : Integer.Sparse Key := [(key739, 2), (key740, -2), (key744, -2), (key745, 2), (key819, -2), (key820, 2), (key826, 2), (key829, -2), (key903, 2), (key904, -2), (key909, -2), (key912, 2)]

def row7076 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7077 : Integer.Sparse Key := [(key739, -1), (key740, 1), (key744, 1), (key745, -1), (key819, 1), (key820, -1), (key826, -1), (key829, 1), (key903, -1), (key904, 1), (key909, 1), (key912, -1)]

def row7078 : Integer.Sparse Key := [(key2093, -4), (key2094, 4), (key2096, 4), (key2097, -4), (key2195, 4), (key2196, -4), (key2201, -4), (key2202, 4), (key2306, -4), (key2307, 4), (key2311, 4), (key2312, -4)]

def row7079 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7080 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7081 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7082 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7083 : Integer.Sparse Key := [(key2093, -4), (key2094, 4), (key2096, 4), (key2097, -4), (key2195, 4), (key2196, -4), (key2201, -4), (key2202, 4), (key2306, -4), (key2307, 4), (key2311, 4), (key2312, -4)]

def row7084 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7085 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7086 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7087 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7088 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7089 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7090 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7091 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7092 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7093 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7094 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7095 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7096 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7097 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7098 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7099 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7100 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7101 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7102 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7103 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7104 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7105 : Integer.Sparse Key := [(key2093, 2), (key2094, -2), (key2096, -2), (key2097, 2), (key2195, -2), (key2196, 2), (key2201, 2), (key2202, -2), (key2306, 2), (key2307, -2), (key2311, -2), (key2312, 2)]

def row7106 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7107 : Integer.Sparse Key := [(key2093, -1), (key2094, 1), (key2096, 1), (key2097, -1), (key2195, 1), (key2196, -1), (key2201, -1), (key2202, 1), (key2306, -1), (key2307, 1), (key2311, 1), (key2312, -1)]

def row7108 : Integer.Sparse Key := [(key717, -4), (key719, 8), (key720, -4), (key894, 4), (key896, -4), (key917, -4), (key920, 4), (key949, -4), (key950, 4), (key956, 4), (key958, -4)]

def row7109 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7110 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7111 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7112 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7113 : Integer.Sparse Key := [(key717, -4), (key719, 8), (key720, -4), (key894, 4), (key896, -4), (key917, -4), (key920, 4), (key949, -4), (key950, 4), (key956, 4), (key958, -4)]

def row7114 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7115 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7116 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7117 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7118 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7119 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7120 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7121 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7122 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7123 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7124 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7125 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7126 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7127 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7128 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7129 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7130 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7131 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7132 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7133 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7134 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7135 : Integer.Sparse Key := [(key717, 2), (key719, -4), (key720, 2), (key894, -2), (key896, 2), (key917, 2), (key920, -2), (key949, 2), (key950, -2), (key956, -2), (key958, 2)]

def row7136 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7137 : Integer.Sparse Key := [(key717, -1), (key719, 2), (key720, -1), (key894, 1), (key896, -1), (key917, -1), (key920, 1), (key949, -1), (key950, 1), (key956, 1), (key958, -1)]

def row7138 : Integer.Sparse Key := [(key2002, -4), (key2004, 8), (key2005, -4), (key2271, 4), (key2273, -4), (key2295, -4), (key2297, 4), (key2325, -4), (key2326, 4), (key2337, 4), (key2338, -4)]

def row7139 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7140 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7141 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7142 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7143 : Integer.Sparse Key := [(key2002, -4), (key2004, 8), (key2005, -4), (key2271, 4), (key2273, -4), (key2295, -4), (key2297, 4), (key2325, -4), (key2326, 4), (key2337, 4), (key2338, -4)]

def row7144 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7145 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7146 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7147 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7148 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7149 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7150 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7151 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7152 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7153 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7154 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7155 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7156 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7157 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7158 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7159 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7160 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7161 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7162 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7163 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7164 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7165 : Integer.Sparse Key := [(key2002, 2), (key2004, -4), (key2005, 2), (key2271, -2), (key2273, 2), (key2295, 2), (key2297, -2), (key2325, 2), (key2326, -2), (key2337, -2), (key2338, 2)]

def row7166 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

def row7167 : Integer.Sparse Key := [(key2002, -1), (key2004, 2), (key2005, -1), (key2271, 1), (key2273, -1), (key2295, -1), (key2297, 1), (key2325, -1), (key2326, 1), (key2337, 1), (key2338, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row7168 : Integer.Sparse Key := [(key2178, -4), (key2180, 4), (key2190, 4), (key2192, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2331, 4), (key2335, 4), (key2339, -4)]

def row7169 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7170 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7171 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7172 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7173 : Integer.Sparse Key := [(key2178, -4), (key2180, 4), (key2190, 4), (key2192, -4), (key2278, 4), (key2282, -4), (key2290, -4), (key2298, 4), (key2329, -4), (key2331, 4), (key2335, 4), (key2339, -4)]

def row7174 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7175 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7176 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7177 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7178 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7179 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7180 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7181 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7182 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7183 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7184 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7185 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7186 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7187 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7188 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7189 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7190 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

def row7191 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7192 : Integer.Sparse Key := [(key2178, 2), (key2180, -2), (key2190, -2), (key2192, 2), (key2278, -2), (key2282, 2), (key2290, 2), (key2298, -2), (key2329, 2), (key2331, -2), (key2335, -2), (key2339, 2)]

def row7193 : Integer.Sparse Key := [(key2178, -1), (key2180, 1), (key2190, 1), (key2192, -1), (key2278, 1), (key2282, -1), (key2290, -1), (key2298, 1), (key2329, -1), (key2331, 1), (key2335, 1), (key2339, -1)]

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

def row7296 : Integer.Sparse Key := [(key822, 1), (key823, -1), (key827, -1), (key828, 1), (key906, -1), (key910, 1), (key911, 1), (key918, -1), (key952, 1), (key953, -2), (key957, 1)]

def row7318 : Integer.Sparse Key := [(key781, -4), (key784, 8), (key786, -4), (key806, 4), (key809, -4), (key814, -4), (key816, 4), (key822, -4), (key823, 4), (key827, 4), (key828, -4)]

def row7319 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7320 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7321 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7322 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7323 : Integer.Sparse Key := [(key781, -4), (key784, 8), (key786, -4), (key806, 4), (key809, -4), (key814, -4), (key816, 4), (key822, -4), (key823, 4), (key827, 4), (key828, -4)]

def row7324 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

def row7325 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -3), (key816, 3), (key822, 1), (key823, -1), (key827, 1), (key828, -1)]

def row7326 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -3), (key816, 3), (key822, 1), (key823, -1), (key827, 1), (key828, -1)]

def row7327 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 4), (key816, -6), (key823, 2), (key827, -2), (key828, 2)]

def row7328 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -2), (key816, 3), (key823, -1), (key827, 1), (key828, -1)]

def row7329 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -2), (key816, 3), (key823, -1), (key827, 1), (key828, -1)]

def row7330 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -6), (key816, 3), (key822, 4), (key823, -1), (key827, 1), (key828, -1)]

def row7331 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -6), (key816, 3), (key822, 4), (key823, -1), (key827, 1), (key828, -1)]

def row7332 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 3), (key822, -1), (key823, -1), (key827, 1), (key828, -1)]

def row7333 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 3), (key822, -1), (key823, -1), (key827, 1), (key828, -1)]

def row7334 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

def row7335 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 6), (key816, -6), (key822, -2), (key823, 2), (key827, -2), (key828, 2)]

def row7336 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

def row7337 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

def row7338 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7339 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7340 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7341 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key816, -2), (key822, 4), (key823, -2), (key827, -2), (key828, 2)]

def row7342 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key816, -2), (key822, 4), (key823, -2), (key827, -2), (key828, 2)]

def row7343 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7344 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, 1), (key816, 1), (key822, -3), (key823, 1), (key827, 1), (key828, -1)]

def row7345 : Integer.Sparse Key := [(key781, 2), (key784, -4), (key786, 2), (key806, -2), (key809, 2), (key814, 2), (key816, -2), (key822, 2), (key823, -2), (key827, -2), (key828, 2)]

def row7346 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

def row7347 : Integer.Sparse Key := [(key781, -1), (key784, 2), (key786, -1), (key806, 1), (key809, -1), (key814, -1), (key816, 1), (key822, -1), (key823, 1), (key827, 1), (key828, -1)]

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

def nodeValue1155 : Sparse Master := [(Sum.inr 1155, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


