-- Prove2me | Definitions.Def_OAIQ106D179
-- name    : OAIQ106D179
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:41:37.239482+00:00
-- url     : https://prove2.me/theorems/1f5d6e2d-1cdf-467a-a813-10b74b8abd72
-- title:
--   Definitions bundle OAIQ106D179 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 147 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow6807`, `OAI.MUB6.Certificate.GramRows.rawRow6808`, `OAI.MUB6.Certificate.GramRows.rawRow6809`, `OAI.MUB6.Certificate.GramRows.rawRow6810`, `OAI.MUB6.Certificate.GramRows.rawRow6811`, `OAI.MUB6.Certificate.GramRows.rawRow6812`, `OAI.MUB6.Certificate.GramRows.rawRow6813`, `OAI.MUB6.Certificate.GramRows.rawRow6814`, `OAI.MUB6.Certificate.GramRows.rawRow6815`, `OAI.MUB6.Certificate.GramRows.rawRow6816`, `OAI.MUB6.Certificate.GramRows.rawRow6817`, `OAI.MUB6.Certificate.GramRows.rawRow6818`, `OAI.MUB6.Certificate.GramRows.rawRow6819`, `OAI.MUB6.Certificate.GramRows.rawRow6820`, `OAI.MUB6.Certificate.GramRows.rawRow6821`, `OAI.MUB6.Certificate.GramRows.rawRow6822`, `OAI.MUB6.Certificate.GramRows.rawRow6823`, `OAI.MUB6.Certificate.GramRows.rawRow6824`, `OAI.MUB6.Certificate.GramRows.rawRow6825`, `OAI.MUB6.Certificate.GramRows.rawRow6826`, `OAI.MUB6.Certificate.GramRows.rawRow6827`, `OAI.MUB6.Certificate.GramRows.rawRow6828`, `OAI.MUB6.Certificate.GramRows.rawRow6829`, `OAI.MUB6.Certificate.GramRows.rawRow6830`, `OAI.MUB6.Certificate.GramRows.rawRow6831`, `OAI.MUB6.Certificate.GramRows.rawRow6832`, `OAI.MUB6.Certificate.GramRows.rawRow6833`, `OAI.MUB6.Certificate.GramRows.rawRow6834`, `OAI.MUB6.Certificate.GramRows.rawRow6835`, `OAI.MUB6.Certificate.GramRows.rawRow6836`, `OAI.MUB6.Certificate.GramRows.rawRow6837`, `OAI.MUB6.Certificate.GramRows.rawRow6838`, `OAI.MUB6.Certificate.GramRows.rawRow6839`, `OAI.MUB6.Certificate.GramRows.rawRow684`, `OAI.MUB6.Certificate.GramRows.rawRow6840`, `OAI.MUB6.Certificate.GramRows.rawRow6841`, `OAI.MUB6.Certificate.GramRows.rawRow6842`, `OAI.MUB6.Certificate.GramRows.rawRow6843`, `OAI.MUB6.Certificate.GramRows.rawRow6844`, `OAI.MUB6.Certificate.GramRows.rawRow6845` and 107 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block18.lean), [`MutuallyUnbiased_GramRows_Block19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block19.lean), [`MutuallyUnbiased_GramRows_Block77`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block77.lean), [`MutuallyUnbiased_GramRows_Block78`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block78.lean), [`MutuallyUnbiased_GramRows_Block82`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block82.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D089`, `OAIQ106D090` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval1_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_2`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_3`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow69 : Integer.Sparse Key := [(key1659, -1), (key1655, -1), (key1667, 2), (key1559, 1), (key1546, 1), (key1667, -1), (key1596, -1), (key1546, -2), (key1655, 1), (key1573, 1), (key1817, 1), (key1813, 1), (key1825, -2), (key1329, -1), (key1316, -1), (key1825, 1), (key1447, 1), (key1316, 2), (key1813, -1), (key1424, -1), (key1780, -1), (key1772, -1), (key1844, 1), (key1798, 1), (key1345, 1), (key1337, 1), (key1844, -1), (key1466, -1), (key1337, -1), (key1296, -1), (key1772, 1), (key1391, 1), (key1774, 2), (key1839, -1), (key1790, -1), (key1339, -2), (key1839, 1), (key1457, 1), (key1339, 1), (key1302, 1), (key1774, -1), (key1397, -1)]

end MUB6.Certificate.GramRows

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

def rawRow684 : Integer.Sparse Key := [(key383, -6), (key433, 2), (key433, 2), (key404, 2), (key246, 6), (key433, -2), (key433, -2), (key314, -2), (key246, -2), (key246, -2), (key234, -2), (key314, 2), (key314, 2), (key300, 2)]

def rawRow685 : Integer.Sparse Key := [(key404, -6), (key383, 2), (key433, 2), (key433, 2), (key314, 6), (key246, -2), (key433, -2), (key433, -2), (key300, -2), (key314, -2), (key314, -2), (key234, 2), (key404, 2), (key404, 2)]

def rawRow686 : Integer.Sparse Key := [(key404, -6), (key433, 2), (key383, 2), (key433, 2), (key314, 6), (key433, -2), (key246, -2), (key433, -2), (key314, -2), (key300, -2), (key314, -2), (key404, 2), (key234, 2), (key404, 2)]

def rawRow687 : Integer.Sparse Key := [(key404, -6), (key433, 2), (key433, 2), (key383, 2), (key314, 6), (key433, -2), (key433, -2), (key246, -2), (key314, -2), (key314, -2), (key300, -2), (key404, 2), (key404, 2), (key234, 2)]

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

def rawRow719 : Integer.Sparse Key := [(key1289, -6), (key1309, 2), (key1350, 2), (key1309, 2), (key1384, 6), (key1539, -2), (key1895, -2), (key1539, -2), (key1417, -2), (key1471, -2), (key1417, -2), (key1566, 2), (key1902, 2), (key1566, 2)]

def rawRow721 : Integer.Sparse Key := [(key1309, -6), (key1289, 2), (key1309, 2), (key1350, 2), (key1539, 6), (key1384, -2), (key1539, -2), (key1895, -2), (key1566, -2), (key1615, -2), (key1680, -2), (key1417, 2), (key1615, 2), (key1917, 2)]

def rawRow722 : Integer.Sparse Key := [(key1309, -6), (key1289, 2), (key1350, 2), (key1309, 2), (key1539, 6), (key1384, -2), (key1895, -2), (key1539, -2), (key1566, -2), (key1680, -2), (key1615, -2), (key1417, 2), (key1917, 2), (key1615, 2)]

def rawRow723 : Integer.Sparse Key := [(key1309, -6), (key1309, 2), (key1289, 2), (key1350, 2), (key1539, 6), (key1539, -2), (key1384, -2), (key1895, -2), (key1615, -2), (key1566, -2), (key1680, -2), (key1615, 2), (key1417, 2), (key1917, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6807 : Integer.Sparse Key := [(key2288, -1), (key2288, -1), (key2254, 2), (key2288, -1), (key2288, -1), (key2188, 2), (key2188, 2), (key2167, -1), (key2167, -1), (key2254, 2), (key2167, -1), (key2167, -1), (key2280, 1), (key2280, 1), (key2247, -2), (key2280, 1), (key2280, 1), (key2086, -2), (key2086, -2), (key2070, 1), (key2070, 1), (key2247, -2), (key2070, 1), (key2070, 1), (key2177, -1), (key2177, -1), (key2153, 1), (key2153, 1), (key2080, 1), (key2080, 1), (key2064, -1), (key2064, -1), (key2177, -1), (key2177, -1), (key2080, 1), (key2080, 1), (key2153, 1), (key2153, 1), (key2064, -1), (key2064, -1)]

def rawRow6808 : Integer.Sparse Key := [(key66, -4), (key66, 2), (key67, 2), (key78, 2), (key80, 2), (key80, -4), (key708, 2), (key708, -1), (key711, -1), (key862, 2), (key862, -1), (key887, -1), (key894, -1), (key896, -1), (key894, -1), (key917, -1), (key896, 2), (key917, 2), (key717, -1), (key719, -1), (key719, 2), (key894, -1), (key896, -1), (key894, 2), (key917, 2), (key896, -1), (key917, -1), (key949, 2), (key949, -1), (key956, -1)]

def rawRow6809 : Integer.Sparse Key := [(key66, -4), (key67, 2), (key66, 2), (key80, 2), (key78, 2), (key80, -4), (key708, 2), (key711, -1), (key708, -1), (key862, 2), (key887, -1), (key862, -1), (key896, -1), (key894, -1), (key917, -1), (key894, -1), (key917, 2), (key896, 2), (key719, -1), (key717, -1), (key719, 2), (key896, -1), (key894, -1), (key917, 2), (key894, 2), (key917, -1), (key896, -1), (key949, 2), (key956, -1), (key949, -1)]

def rawRow6810 : Integer.Sparse Key := [(key67, -4), (key66, 2), (key66, 2), (key80, 2), (key80, 2), (key78, -4), (key711, 2), (key708, -1), (key708, -1), (key887, 2), (key862, -1), (key862, -1), (key917, -1), (key917, -1), (key896, -1), (key896, -1), (key894, 2), (key894, 2), (key719, -1), (key719, -1), (key717, 2), (key917, -1), (key917, -1), (key896, 2), (key896, 2), (key894, -1), (key894, -1), (key956, 2), (key949, -1), (key949, -1)]

def rawRow6811 : Integer.Sparse Key := [(key66, -4), (key78, 2), (key80, 2), (key66, 2), (key67, 2), (key80, -4), (key862, 2), (key894, -1), (key896, -1), (key708, 2), (key894, -1), (key917, -1), (key708, -1), (key711, -1), (key862, -1), (key887, -1), (key896, 2), (key917, 2), (key894, -1), (key896, -1), (key949, 2), (key717, -1), (key719, -1), (key894, 2), (key917, 2), (key949, -1), (key956, -1), (key719, 2), (key896, -1), (key917, -1)]

def rawRow6812 : Integer.Sparse Key := [(key66, -4), (key80, 2), (key78, 2), (key67, 2), (key66, 2), (key80, -4), (key862, 2), (key896, -1), (key894, -1), (key708, 2), (key917, -1), (key894, -1), (key711, -1), (key708, -1), (key887, -1), (key862, -1), (key917, 2), (key896, 2), (key896, -1), (key894, -1), (key949, 2), (key719, -1), (key717, -1), (key917, 2), (key894, 2), (key956, -1), (key949, -1), (key719, 2), (key917, -1), (key896, -1)]

def rawRow6813 : Integer.Sparse Key := [(key78, -4), (key66, 2), (key80, 2), (key66, 2), (key80, 2), (key67, -4), (key894, 2), (key862, -1), (key896, -1), (key894, 2), (key708, -1), (key917, -1), (key862, -1), (key896, -1), (key708, -1), (key917, -1), (key711, 2), (key887, 2), (key894, -1), (key949, -1), (key896, 2), (key894, -1), (key949, -1), (key717, 2), (key956, 2), (key719, -1), (key917, -1), (key896, 2), (key719, -1), (key917, -1)]

def rawRow6814 : Integer.Sparse Key := [(key78, -4), (key80, 2), (key66, 2), (key80, 2), (key66, 2), (key67, -4), (key894, 2), (key896, -1), (key862, -1), (key894, 2), (key917, -1), (key708, -1), (key896, -1), (key862, -1), (key917, -1), (key708, -1), (key887, 2), (key711, 2), (key949, -1), (key894, -1), (key896, 2), (key949, -1), (key894, -1), (key956, 2), (key717, 2), (key917, -1), (key719, -1), (key896, 2), (key917, -1), (key719, -1)]

def rawRow6815 : Integer.Sparse Key := [(key80, -4), (key66, 2), (key78, 2), (key67, 2), (key80, 2), (key66, -4), (key896, 2), (key862, -1), (key894, -1), (key917, 2), (key708, -1), (key894, -1), (key887, -1), (key917, -1), (key711, -1), (key896, -1), (key708, 2), (key862, 2), (key896, -1), (key949, -1), (key894, 2), (key917, -1), (key956, -1), (key719, 2), (key949, 2), (key717, -1), (key894, -1), (key917, 2), (key719, -1), (key896, -1)]

def rawRow6816 : Integer.Sparse Key := [(key80, -4), (key78, 2), (key66, 2), (key80, 2), (key67, 2), (key66, -4), (key896, 2), (key894, -1), (key862, -1), (key917, 2), (key894, -1), (key708, -1), (key917, -1), (key887, -1), (key896, -1), (key711, -1), (key862, 2), (key708, 2), (key949, -1), (key896, -1), (key894, 2), (key956, -1), (key917, -1), (key949, 2), (key719, 2), (key894, -1), (key717, -1), (key917, 2), (key896, -1), (key719, -1)]

def rawRow6817 : Integer.Sparse Key := [(key67, -4), (key80, 2), (key80, 2), (key66, 2), (key66, 2), (key78, -4), (key887, 2), (key917, -1), (key917, -1), (key711, 2), (key896, -1), (key896, -1), (key708, -1), (key708, -1), (key862, -1), (key862, -1), (key894, 2), (key894, 2), (key917, -1), (key917, -1), (key956, 2), (key719, -1), (key719, -1), (key896, 2), (key896, 2), (key949, -1), (key949, -1), (key717, 2), (key894, -1), (key894, -1)]

def rawRow6818 : Integer.Sparse Key := [(key80, -4), (key67, 2), (key80, 2), (key66, 2), (key78, 2), (key66, -4), (key917, 2), (key887, -1), (key917, -1), (key896, 2), (key711, -1), (key896, -1), (key862, -1), (key894, -1), (key708, -1), (key894, -1), (key708, 2), (key862, 2), (key917, -1), (key956, -1), (key917, 2), (key896, -1), (key949, -1), (key719, 2), (key949, 2), (key719, -1), (key896, -1), (key894, 2), (key717, -1), (key894, -1)]

def rawRow6819 : Integer.Sparse Key := [(key80, -4), (key80, 2), (key67, 2), (key78, 2), (key66, 2), (key66, -4), (key917, 2), (key917, -1), (key887, -1), (key896, 2), (key896, -1), (key711, -1), (key894, -1), (key862, -1), (key894, -1), (key708, -1), (key862, 2), (key708, 2), (key956, -1), (key917, -1), (key917, 2), (key949, -1), (key896, -1), (key949, 2), (key719, 2), (key896, -1), (key719, -1), (key894, 2), (key894, -1), (key717, -1)]

def rawRow6820 : Integer.Sparse Key := [(key131, -4), (key141, 2), (key143, 2), (key141, 2), (key143, 2), (key160, -4), (key66, 2), (key78, -1), (key80, -1), (key708, 2), (key894, -1), (key917, -1), (key717, -1), (key719, -1), (key894, -1), (key917, -1), (key949, 2), (key956, 2), (key708, -1), (key711, -1), (key719, 2), (key708, -1), (key711, -1), (key862, 2), (key887, 2), (key896, -1), (key917, -1), (key719, 2), (key896, -1), (key917, -1)]

def rawRow6821 : Integer.Sparse Key := [(key131, -4), (key143, 2), (key141, 2), (key143, 2), (key141, 2), (key160, -4), (key66, 2), (key80, -1), (key78, -1), (key708, 2), (key917, -1), (key894, -1), (key719, -1), (key717, -1), (key917, -1), (key894, -1), (key956, 2), (key949, 2), (key711, -1), (key708, -1), (key719, 2), (key711, -1), (key708, -1), (key887, 2), (key862, 2), (key917, -1), (key896, -1), (key719, 2), (key917, -1), (key896, -1)]

def rawRow6822 : Integer.Sparse Key := [(key141, -4), (key131, 2), (key143, 2), (key141, 2), (key160, 2), (key143, -4), (key78, 2), (key66, -1), (key80, -1), (key894, 2), (key708, -1), (key917, -1), (key894, -1), (key949, -1), (key717, -1), (key956, -1), (key719, 2), (key917, 2), (key708, -1), (key719, -1), (key711, 2), (key862, -1), (key896, -1), (key708, 2), (key917, 2), (key711, -1), (key887, -1), (key896, 2), (key719, -1), (key917, -1)]

def rawRow6823 : Integer.Sparse Key := [(key141, -4), (key143, 2), (key131, 2), (key160, 2), (key141, 2), (key143, -4), (key78, 2), (key80, -1), (key66, -1), (key894, 2), (key917, -1), (key708, -1), (key949, -1), (key894, -1), (key956, -1), (key717, -1), (key917, 2), (key719, 2), (key719, -1), (key708, -1), (key711, 2), (key896, -1), (key862, -1), (key917, 2), (key708, 2), (key887, -1), (key711, -1), (key896, 2), (key917, -1), (key719, -1)]

def rawRow6824 : Integer.Sparse Key := [(key143, -4), (key131, 2), (key141, 2), (key143, 2), (key160, 2), (key141, -4), (key80, 2), (key66, -1), (key78, -1), (key917, 2), (key708, -1), (key894, -1), (key917, -1), (key956, -1), (key719, -1), (key949, -1), (key717, 2), (key894, 2), (key711, -1), (key719, -1), (key708, 2), (key887, -1), (key917, -1), (key711, 2), (key896, 2), (key708, -1), (key862, -1), (key917, 2), (key719, -1), (key896, -1)]

def rawRow6825 : Integer.Sparse Key := [(key143, -4), (key141, 2), (key131, 2), (key160, 2), (key143, 2), (key141, -4), (key80, 2), (key78, -1), (key66, -1), (key917, 2), (key894, -1), (key708, -1), (key956, -1), (key917, -1), (key949, -1), (key719, -1), (key894, 2), (key717, 2), (key719, -1), (key711, -1), (key708, 2), (key917, -1), (key887, -1), (key896, 2), (key711, 2), (key862, -1), (key708, -1), (key917, 2), (key896, -1), (key719, -1)]

def rawRow6826 : Integer.Sparse Key := [(key141, -4), (key141, 2), (key160, 2), (key131, 2), (key143, 2), (key143, -4), (key141, 2), (key141, -1), (key160, -1), (key78, 2), (key717, -1), (key956, -1), (key708, -1), (key719, -1), (key708, -1), (key917, -1), (key719, 2), (key917, 2), (key862, -1), (key896, -1), (key896, 2), (key708, -1), (key719, -1), (key708, 2), (key917, 2), (key719, -1), (key917, -1), (key711, 2), (key711, -1), (key887, -1)]

def rawRow6827 : Integer.Sparse Key := [(key141, -4), (key160, 2), (key141, 2), (key143, 2), (key131, 2), (key143, -4), (key141, 2), (key160, -1), (key141, -1), (key78, 2), (key956, -1), (key717, -1), (key719, -1), (key708, -1), (key917, -1), (key708, -1), (key917, 2), (key719, 2), (key896, -1), (key862, -1), (key896, 2), (key719, -1), (key708, -1), (key917, 2), (key708, 2), (key917, -1), (key719, -1), (key711, 2), (key887, -1), (key711, -1)]

def rawRow6828 : Integer.Sparse Key := [(key160, -4), (key141, 2), (key141, 2), (key143, 2), (key143, 2), (key131, -4), (key160, 2), (key141, -1), (key141, -1), (key191, 2), (key78, -1), (key717, -1), (key917, -1), (key917, -1), (key719, -1), (key719, -1), (key708, 2), (key708, 2), (key896, -1), (key896, -1), (key862, 2), (key917, -1), (key917, -1), (key719, 2), (key719, 2), (key708, -1), (key708, -1), (key887, 2), (key711, -1), (key711, -1)]

def rawRow6829 : Integer.Sparse Key := [(key143, -4), (key143, 2), (key160, 2), (key131, 2), (key141, 2), (key141, -4), (key183, 2), (key183, -1), (key191, -1), (key80, 2), (key80, -1), (key160, -1), (key66, -1), (key78, -1), (key708, -1), (key894, -1), (key717, 2), (key894, 2), (key887, -1), (key917, -1), (key917, 2), (key711, -1), (key719, -1), (key711, 2), (key896, 2), (key719, -1), (key896, -1), (key708, 2), (key708, -1), (key862, -1)]

def rawRow6830 : Integer.Sparse Key := [(key143, -4), (key160, 2), (key143, 2), (key141, 2), (key131, 2), (key141, -4), (key183, 2), (key191, -1), (key183, -1), (key80, 2), (key160, -1), (key80, -1), (key78, -1), (key66, -1), (key894, -1), (key708, -1), (key894, 2), (key717, 2), (key917, -1), (key887, -1), (key917, 2), (key719, -1), (key711, -1), (key896, 2), (key711, 2), (key896, -1), (key719, -1), (key708, 2), (key862, -1), (key708, -1)]

def rawRow6831 : Integer.Sparse Key := [(key160, -4), (key143, 2), (key143, 2), (key141, 2), (key141, 2), (key131, -4), (key191, 2), (key183, -1), (key183, -1), (key160, 2), (key80, -1), (key80, -1), (key141, -1), (key141, -1), (key78, -1), (key717, -1), (key708, 2), (key708, 2), (key917, -1), (key917, -1), (key887, 2), (key896, -1), (key896, -1), (key719, 2), (key719, 2), (key711, -1), (key711, -1), (key862, 2), (key708, -1), (key708, -1)]

def rawRow6832 : Integer.Sparse Key := [(key178, -4), (key183, 2), (key183, 2), (key183, 2), (key183, 2), (key191, -4), (key67, 2), (key80, -1), (key80, -1), (key67, 2), (key143, -1), (key143, -1), (key80, -1), (key80, -1), (key143, -1), (key143, -1), (key160, 2), (key160, 2), (key66, -1), (key66, -1), (key78, 2), (key708, -1), (key708, -1), (key862, 2), (key862, 2), (key894, -1), (key894, -1), (key717, 2), (key894, -1), (key894, -1)]

def rawRow6833 : Integer.Sparse Key := [(key183, -4), (key178, 2), (key183, 2), (key183, 2), (key191, 2), (key183, -4), (key80, 2), (key67, -1), (key80, -1), (key143, 2), (key67, -1), (key143, -1), (key143, -1), (key160, -1), (key80, -1), (key160, -1), (key80, 2), (key143, 2), (key66, -1), (key78, -1), (key66, 2), (key862, -1), (key894, -1), (key708, 2), (key894, 2), (key708, -1), (key862, -1), (key894, 2), (key717, -1), (key894, -1)]

def rawRow6834 : Integer.Sparse Key := [(key183, -4), (key183, 2), (key178, 2), (key191, 2), (key183, 2), (key183, -4), (key80, 2), (key80, -1), (key67, -1), (key143, 2), (key143, -1), (key67, -1), (key160, -1), (key143, -1), (key160, -1), (key80, -1), (key143, 2), (key80, 2), (key78, -1), (key66, -1), (key66, 2), (key894, -1), (key862, -1), (key894, 2), (key708, 2), (key862, -1), (key708, -1), (key894, 2), (key894, -1), (key717, -1)]

def rawRow6835 : Integer.Sparse Key := [(key183, -4), (key183, 2), (key191, 2), (key178, 2), (key183, 2), (key183, -4), (key143, 2), (key143, -1), (key160, -1), (key80, 2), (key80, -1), (key160, -1), (key67, -1), (key80, -1), (key67, -1), (key143, -1), (key80, 2), (key143, 2), (key131, -1), (key141, -1), (key141, 2), (key66, -1), (key78, -1), (key708, 2), (key894, 2), (key717, -1), (key894, -1), (key708, 2), (key708, -1), (key862, -1)]

def rawRow6836 : Integer.Sparse Key := [(key183, -4), (key191, 2), (key183, 2), (key183, 2), (key178, 2), (key183, -4), (key143, 2), (key160, -1), (key143, -1), (key80, 2), (key160, -1), (key80, -1), (key80, -1), (key67, -1), (key143, -1), (key67, -1), (key143, 2), (key80, 2), (key141, -1), (key131, -1), (key141, 2), (key78, -1), (key66, -1), (key894, 2), (key708, 2), (key894, -1), (key717, -1), (key708, 2), (key862, -1), (key708, -1)]

def rawRow6837 : Integer.Sparse Key := [(key191, -4), (key183, 2), (key183, 2), (key183, 2), (key183, 2), (key178, -4), (key160, 2), (key143, -1), (key143, -1), (key160, 2), (key80, -1), (key80, -1), (key143, -1), (key143, -1), (key80, -1), (key80, -1), (key67, 2), (key67, 2), (key141, -1), (key141, -1), (key131, 2), (key141, -1), (key141, -1), (key78, 2), (key717, 2), (key708, -1), (key708, -1), (key862, 2), (key708, -1), (key708, -1)]

def rawRow6838 : Integer.Sparse Key := [(key1992, -4), (key1992, 2), (key1995, 2), (key2002, 2), (key2004, 2), (key2004, -4), (key1992, 2), (key1992, -1), (key1995, -1), (key2237, 2), (key2237, -1), (key2260, -1), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, 2), (key2295, 2), (key2002, -1), (key2004, -1), (key2004, 2), (key2271, -1), (key2273, -1), (key2271, 2), (key2295, 2), (key2273, -1), (key2295, -1), (key2325, 2), (key2325, -1), (key2337, -1)]

def rawRow6839 : Integer.Sparse Key := [(key1992, -4), (key1995, 2), (key1992, 2), (key2004, 2), (key2002, 2), (key2004, -4), (key1992, 2), (key1995, -1), (key1992, -1), (key2237, 2), (key2260, -1), (key2237, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, 2), (key2273, 2), (key2004, -1), (key2002, -1), (key2004, 2), (key2273, -1), (key2271, -1), (key2295, 2), (key2271, 2), (key2295, -1), (key2273, -1), (key2325, 2), (key2337, -1), (key2325, -1)]

def rawRow6840 : Integer.Sparse Key := [(key1995, -4), (key1992, 2), (key1992, 2), (key2004, 2), (key2004, 2), (key2002, -4), (key1995, 2), (key1992, -1), (key1992, -1), (key2260, 2), (key2237, -1), (key2237, -1), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, 2), (key2271, 2), (key2004, -1), (key2004, -1), (key2002, 2), (key2295, -1), (key2295, -1), (key2273, 2), (key2273, 2), (key2271, -1), (key2271, -1), (key2337, 2), (key2325, -1), (key2325, -1)]

def rawRow6841 : Integer.Sparse Key := [(key1992, -4), (key2002, 2), (key2004, 2), (key1992, 2), (key1995, 2), (key2004, -4), (key2237, 2), (key2271, -1), (key2273, -1), (key1992, 2), (key2271, -1), (key2295, -1), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, 2), (key2295, 2), (key2271, -1), (key2273, -1), (key2325, 2), (key2002, -1), (key2004, -1), (key2271, 2), (key2295, 2), (key2325, -1), (key2337, -1), (key2004, 2), (key2273, -1), (key2295, -1)]

def rawRow6842 : Integer.Sparse Key := [(key1992, -4), (key2004, 2), (key2002, 2), (key1995, 2), (key1992, 2), (key2004, -4), (key2237, 2), (key2273, -1), (key2271, -1), (key1992, 2), (key2295, -1), (key2271, -1), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, 2), (key2273, 2), (key2273, -1), (key2271, -1), (key2325, 2), (key2004, -1), (key2002, -1), (key2295, 2), (key2271, 2), (key2337, -1), (key2325, -1), (key2004, 2), (key2295, -1), (key2273, -1)]

def rawRow6843 : Integer.Sparse Key := [(key2002, -4), (key1992, 2), (key2004, 2), (key1992, 2), (key2004, 2), (key1995, -4), (key2271, 2), (key2237, -1), (key2273, -1), (key2271, 2), (key1992, -1), (key2295, -1), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, 2), (key2260, 2), (key2271, -1), (key2325, -1), (key2273, 2), (key2271, -1), (key2325, -1), (key2002, 2), (key2337, 2), (key2004, -1), (key2295, -1), (key2273, 2), (key2004, -1), (key2295, -1)]

def rawRow6844 : Integer.Sparse Key := [(key2002, -4), (key2004, 2), (key1992, 2), (key2004, 2), (key1992, 2), (key1995, -4), (key2271, 2), (key2273, -1), (key2237, -1), (key2271, 2), (key2295, -1), (key1992, -1), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, 2), (key1995, 2), (key2325, -1), (key2271, -1), (key2273, 2), (key2325, -1), (key2271, -1), (key2337, 2), (key2002, 2), (key2295, -1), (key2004, -1), (key2273, 2), (key2295, -1), (key2004, -1)]

def rawRow6845 : Integer.Sparse Key := [(key2004, -4), (key1992, 2), (key2002, 2), (key1995, 2), (key2004, 2), (key1992, -4), (key2273, 2), (key2237, -1), (key2271, -1), (key2295, 2), (key1992, -1), (key2271, -1), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, 2), (key2237, 2), (key2273, -1), (key2325, -1), (key2271, 2), (key2295, -1), (key2337, -1), (key2004, 2), (key2325, 2), (key2002, -1), (key2271, -1), (key2295, 2), (key2004, -1), (key2273, -1)]

def rawRow6846 : Integer.Sparse Key := [(key2004, -4), (key2002, 2), (key1992, 2), (key2004, 2), (key1995, 2), (key1992, -4), (key2273, 2), (key2271, -1), (key2237, -1), (key2295, 2), (key2271, -1), (key1992, -1), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, 2), (key1992, 2), (key2325, -1), (key2273, -1), (key2271, 2), (key2337, -1), (key2295, -1), (key2325, 2), (key2004, 2), (key2271, -1), (key2002, -1), (key2295, 2), (key2273, -1), (key2004, -1)]

def rawRow6847 : Integer.Sparse Key := [(key1995, -4), (key2004, 2), (key2004, 2), (key1992, 2), (key1992, 2), (key2002, -4), (key2260, 2), (key2295, -1), (key2295, -1), (key1995, 2), (key2273, -1), (key2273, -1), (key1992, -1), (key1992, -1), (key2237, -1), (key2237, -1), (key2271, 2), (key2271, 2), (key2295, -1), (key2295, -1), (key2337, 2), (key2004, -1), (key2004, -1), (key2273, 2), (key2273, 2), (key2325, -1), (key2325, -1), (key2002, 2), (key2271, -1), (key2271, -1)]

def rawRow6848 : Integer.Sparse Key := [(key2004, -4), (key1995, 2), (key2004, 2), (key1992, 2), (key2002, 2), (key1992, -4), (key2295, 2), (key2260, -1), (key2295, -1), (key2273, 2), (key1995, -1), (key2273, -1), (key2237, -1), (key2271, -1), (key1992, -1), (key2271, -1), (key1992, 2), (key2237, 2), (key2295, -1), (key2337, -1), (key2295, 2), (key2273, -1), (key2325, -1), (key2004, 2), (key2325, 2), (key2004, -1), (key2273, -1), (key2271, 2), (key2002, -1), (key2271, -1)]

def rawRow6849 : Integer.Sparse Key := [(key2004, -4), (key2004, 2), (key1995, 2), (key2002, 2), (key1992, 2), (key1992, -4), (key2295, 2), (key2295, -1), (key2260, -1), (key2273, 2), (key2273, -1), (key1995, -1), (key2271, -1), (key2237, -1), (key2271, -1), (key1992, -1), (key2237, 2), (key1992, 2), (key2337, -1), (key2295, -1), (key2295, 2), (key2325, -1), (key2273, -1), (key2325, 2), (key2004, 2), (key2273, -1), (key2004, -1), (key2271, 2), (key2271, -1), (key2002, -1)]

def rawRow6850 : Integer.Sparse Key := [(key2237, -4), (key2271, 2), (key2273, 2), (key2271, 2), (key2273, 2), (key2325, -4), (key1992, 2), (key2002, -1), (key2004, -1), (key1992, 2), (key2271, -1), (key2295, -1), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, 2), (key2337, 2), (key1992, -1), (key1995, -1), (key2004, 2), (key1992, -1), (key1995, -1), (key2237, 2), (key2260, 2), (key2273, -1), (key2295, -1), (key2004, 2), (key2273, -1), (key2295, -1)]

def rawRow6851 : Integer.Sparse Key := [(key2237, -4), (key2273, 2), (key2271, 2), (key2273, 2), (key2271, 2), (key2325, -4), (key1992, 2), (key2004, -1), (key2002, -1), (key1992, 2), (key2295, -1), (key2271, -1), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, 2), (key2325, 2), (key1995, -1), (key1992, -1), (key2004, 2), (key1995, -1), (key1992, -1), (key2260, 2), (key2237, 2), (key2295, -1), (key2273, -1), (key2004, 2), (key2295, -1), (key2273, -1)]

def rawRow6852 : Integer.Sparse Key := [(key2271, -4), (key2237, 2), (key2273, 2), (key2271, 2), (key2325, 2), (key2273, -4), (key2002, 2), (key1992, -1), (key2004, -1), (key2271, 2), (key1992, -1), (key2295, -1), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, 2), (key2295, 2), (key1992, -1), (key2004, -1), (key1995, 2), (key2237, -1), (key2273, -1), (key1992, 2), (key2295, 2), (key1995, -1), (key2260, -1), (key2273, 2), (key2004, -1), (key2295, -1)]

def rawRow6853 : Integer.Sparse Key := [(key2271, -4), (key2273, 2), (key2237, 2), (key2325, 2), (key2271, 2), (key2273, -4), (key2002, 2), (key2004, -1), (key1992, -1), (key2271, 2), (key2295, -1), (key1992, -1), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, 2), (key2004, 2), (key2004, -1), (key1992, -1), (key1995, 2), (key2273, -1), (key2237, -1), (key2295, 2), (key1992, 2), (key2260, -1), (key1995, -1), (key2273, 2), (key2295, -1), (key2004, -1)]

def rawRow6854 : Integer.Sparse Key := [(key2273, -4), (key2237, 2), (key2271, 2), (key2273, 2), (key2325, 2), (key2271, -4), (key2004, 2), (key1992, -1), (key2002, -1), (key2295, 2), (key1992, -1), (key2271, -1), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, 2), (key2271, 2), (key1995, -1), (key2004, -1), (key1992, 2), (key2260, -1), (key2295, -1), (key1995, 2), (key2273, 2), (key1992, -1), (key2237, -1), (key2295, 2), (key2004, -1), (key2273, -1)]

def rawRow6855 : Integer.Sparse Key := [(key2273, -4), (key2271, 2), (key2237, 2), (key2325, 2), (key2273, 2), (key2271, -4), (key2004, 2), (key2002, -1), (key1992, -1), (key2295, 2), (key2271, -1), (key1992, -1), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, 2), (key2002, 2), (key2004, -1), (key1995, -1), (key1992, 2), (key2295, -1), (key2260, -1), (key2273, 2), (key1995, 2), (key2237, -1), (key1992, -1), (key2295, 2), (key2273, -1), (key2004, -1)]

def rawRow6856 : Integer.Sparse Key := [(key2271, -4), (key2271, 2), (key2325, 2), (key2237, 2), (key2273, 2), (key2273, -4), (key2271, 2), (key2271, -1), (key2325, -1), (key2002, 2), (key2002, -1), (key2337, -1), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, 2), (key2295, 2), (key2237, -1), (key2273, -1), (key2273, 2), (key1992, -1), (key2004, -1), (key1992, 2), (key2295, 2), (key2004, -1), (key2295, -1), (key1995, 2), (key1995, -1), (key2260, -1)]

def rawRow6857 : Integer.Sparse Key := [(key2271, -4), (key2325, 2), (key2271, 2), (key2273, 2), (key2237, 2), (key2273, -4), (key2271, 2), (key2325, -1), (key2271, -1), (key2002, 2), (key2337, -1), (key2002, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, 2), (key2004, 2), (key2273, -1), (key2237, -1), (key2273, 2), (key2004, -1), (key1992, -1), (key2295, 2), (key1992, 2), (key2295, -1), (key2004, -1), (key1995, 2), (key2260, -1), (key1995, -1)]

def rawRow6858 : Integer.Sparse Key := [(key2325, -4), (key2271, 2), (key2271, 2), (key2273, 2), (key2273, 2), (key2237, -4), (key2325, 2), (key2271, -1), (key2271, -1), (key2337, 2), (key2002, -1), (key2002, -1), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, 2), (key1992, 2), (key2273, -1), (key2273, -1), (key2237, 2), (key2295, -1), (key2295, -1), (key2004, 2), (key2004, 2), (key1992, -1), (key1992, -1), (key2260, 2), (key1995, -1), (key1995, -1)]

def rawRow6859 : Integer.Sparse Key := [(key2273, -4), (key2273, 2), (key2325, 2), (key2237, 2), (key2271, 2), (key2271, -4), (key2295, 2), (key2295, -1), (key2337, -1), (key2004, 2), (key2004, -1), (key2325, -1), (key1992, -1), (key2002, -1), (key1992, -1), (key2271, -1), (key2002, 2), (key2271, 2), (key2260, -1), (key2295, -1), (key2295, 2), (key1995, -1), (key2004, -1), (key1995, 2), (key2273, 2), (key2004, -1), (key2273, -1), (key1992, 2), (key1992, -1), (key2237, -1)]

def rawRow6860 : Integer.Sparse Key := [(key2273, -4), (key2325, 2), (key2273, 2), (key2271, 2), (key2237, 2), (key2271, -4), (key2295, 2), (key2337, -1), (key2295, -1), (key2004, 2), (key2325, -1), (key2004, -1), (key2002, -1), (key1992, -1), (key2271, -1), (key1992, -1), (key2271, 2), (key2002, 2), (key2295, -1), (key2260, -1), (key2295, 2), (key2004, -1), (key1995, -1), (key2273, 2), (key1995, 2), (key2273, -1), (key2004, -1), (key1992, 2), (key2237, -1), (key1992, -1)]

def rawRow6861 : Integer.Sparse Key := [(key2325, -4), (key2273, 2), (key2273, 2), (key2271, 2), (key2271, 2), (key2237, -4), (key2337, 2), (key2295, -1), (key2295, -1), (key2325, 2), (key2004, -1), (key2004, -1), (key2271, -1), (key2271, -1), (key2002, -1), (key2002, -1), (key1992, 2), (key1992, 2), (key2295, -1), (key2295, -1), (key2260, 2), (key2273, -1), (key2273, -1), (key2004, 2), (key2004, 2), (key1995, -1), (key1995, -1), (key2237, 2), (key1992, -1), (key1992, -1)]

def rawRow6862 : Integer.Sparse Key := [(key2260, -4), (key2295, 2), (key2295, 2), (key2295, 2), (key2295, 2), (key2337, -4), (key1995, 2), (key2004, -1), (key2004, -1), (key1995, 2), (key2273, -1), (key2273, -1), (key2004, -1), (key2004, -1), (key2273, -1), (key2273, -1), (key2325, 2), (key2325, 2), (key1992, -1), (key1992, -1), (key2002, 2), (key1992, -1), (key1992, -1), (key2237, 2), (key2237, 2), (key2271, -1), (key2271, -1), (key2002, 2), (key2271, -1), (key2271, -1)]

def rawRow6863 : Integer.Sparse Key := [(key2295, -4), (key2260, 2), (key2295, 2), (key2295, 2), (key2337, 2), (key2295, -4), (key2004, 2), (key1995, -1), (key2004, -1), (key2273, 2), (key1995, -1), (key2273, -1), (key2273, -1), (key2325, -1), (key2004, -1), (key2325, -1), (key2004, 2), (key2273, 2), (key1992, -1), (key2002, -1), (key1992, 2), (key2237, -1), (key2271, -1), (key1992, 2), (key2271, 2), (key1992, -1), (key2237, -1), (key2271, 2), (key2002, -1), (key2271, -1)]

def rawRow6864 : Integer.Sparse Key := [(key2295, -4), (key2295, 2), (key2260, 2), (key2337, 2), (key2295, 2), (key2295, -4), (key2004, 2), (key2004, -1), (key1995, -1), (key2273, 2), (key2273, -1), (key1995, -1), (key2325, -1), (key2273, -1), (key2325, -1), (key2004, -1), (key2273, 2), (key2004, 2), (key2002, -1), (key1992, -1), (key1992, 2), (key2271, -1), (key2237, -1), (key2271, 2), (key1992, 2), (key2237, -1), (key1992, -1), (key2271, 2), (key2271, -1), (key2002, -1)]

def rawRow6865 : Integer.Sparse Key := [(key2295, -4), (key2295, 2), (key2337, 2), (key2260, 2), (key2295, 2), (key2295, -4), (key2273, 2), (key2273, -1), (key2325, -1), (key2004, 2), (key2004, -1), (key2325, -1), (key1995, -1), (key2004, -1), (key1995, -1), (key2273, -1), (key2004, 2), (key2273, 2), (key2237, -1), (key2271, -1), (key2271, 2), (key1992, -1), (key2002, -1), (key1992, 2), (key2271, 2), (key2002, -1), (key2271, -1), (key1992, 2), (key1992, -1), (key2237, -1)]

def rawRow6866 : Integer.Sparse Key := [(key2295, -4), (key2337, 2), (key2295, 2), (key2295, 2), (key2260, 2), (key2295, -4), (key2273, 2), (key2325, -1), (key2273, -1), (key2004, 2), (key2325, -1), (key2004, -1), (key2004, -1), (key1995, -1), (key2273, -1), (key1995, -1), (key2273, 2), (key2004, 2), (key2271, -1), (key2237, -1), (key2271, 2), (key2002, -1), (key1992, -1), (key2271, 2), (key1992, 2), (key2271, -1), (key2002, -1), (key1992, 2), (key2237, -1), (key1992, -1)]

def rawRow6867 : Integer.Sparse Key := [(key2337, -4), (key2295, 2), (key2295, 2), (key2295, 2), (key2295, 2), (key2260, -4), (key2325, 2), (key2273, -1), (key2273, -1), (key2325, 2), (key2004, -1), (key2004, -1), (key2273, -1), (key2273, -1), (key2004, -1), (key2004, -1), (key1995, 2), (key1995, 2), (key2271, -1), (key2271, -1), (key2237, 2), (key2271, -1), (key2271, -1), (key2002, 2), (key2002, 2), (key1992, -1), (key1992, -1), (key2237, 2), (key1992, -1), (key1992, -1)]

def rawRow6868 : Integer.Sparse Key := [(key2035, -2), (key2035, 1), (key2038, 1), (key2154, -2), (key2154, 1), (key2170, 1), (key2178, 1), (key2180, 1), (key2178, 1), (key2190, 1), (key2180, -2), (key2190, -2), (key2065, 2), (key2065, -1), (key2073, -1), (key2154, 2), (key2154, -1), (key2170, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, 2), (key2290, 2), (key2081, -1), (key2083, -1), (key2081, 1), (key2088, 1), (key2178, -1), (key2180, -1), (key2180, 1), (key2190, 1), (key2278, 1), (key2282, 1), (key2282, -1), (key2290, -1), (key2329, 1), (key2334, 1), (key2331, -1), (key2334, -1)]

def rawRow6869 : Integer.Sparse Key := [(key2035, -2), (key2038, 1), (key2035, 1), (key2154, -2), (key2170, 1), (key2154, 1), (key2180, 1), (key2178, 1), (key2190, 1), (key2178, 1), (key2190, -2), (key2180, -2), (key2065, 2), (key2073, -1), (key2065, -1), (key2154, 2), (key2170, -1), (key2154, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, 2), (key2282, 2), (key2083, -1), (key2081, -1), (key2088, 1), (key2081, 1), (key2180, -1), (key2178, -1), (key2190, 1), (key2180, 1), (key2282, 1), (key2278, 1), (key2290, -1), (key2282, -1), (key2334, 1), (key2329, 1), (key2334, -1), (key2331, -1)]

def rawRow6870 : Integer.Sparse Key := [(key2038, -2), (key2035, 1), (key2035, 1), (key2170, -2), (key2154, 1), (key2154, 1), (key2190, 1), (key2190, 1), (key2180, 1), (key2180, 1), (key2178, -2), (key2178, -2), (key2073, 2), (key2065, -1), (key2065, -1), (key2170, 2), (key2154, -1), (key2154, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, 2), (key2278, 2), (key2088, -1), (key2088, -1), (key2083, 1), (key2083, 1), (key2190, -1), (key2190, -1), (key2178, 1), (key2178, 1), (key2290, 1), (key2290, 1), (key2278, -1), (key2278, -1), (key2331, 1), (key2331, 1), (key2329, -1), (key2329, -1)]

def rawRow6871 : Integer.Sparse Key := [(key2154, -2), (key2178, 1), (key2180, 1), (key2035, -2), (key2178, 1), (key2190, 1), (key2035, 1), (key2038, 1), (key2154, 1), (key2170, 1), (key2180, -2), (key2190, -2), (key2154, 2), (key2278, -1), (key2282, -1), (key2065, 2), (key2278, -1), (key2290, -1), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, 2), (key2290, 2), (key2178, -1), (key2180, -1), (key2278, 1), (key2282, 1), (key2081, -1), (key2083, -1), (key2329, 1), (key2334, 1), (key2081, 1), (key2088, 1), (key2331, -1), (key2334, -1), (key2180, 1), (key2190, 1), (key2282, -1), (key2290, -1)]

def rawRow6872 : Integer.Sparse Key := [(key2154, -2), (key2180, 1), (key2178, 1), (key2035, -2), (key2190, 1), (key2178, 1), (key2038, 1), (key2035, 1), (key2170, 1), (key2154, 1), (key2190, -2), (key2180, -2), (key2154, 2), (key2282, -1), (key2278, -1), (key2065, 2), (key2290, -1), (key2278, -1), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, 2), (key2282, 2), (key2180, -1), (key2178, -1), (key2282, 1), (key2278, 1), (key2083, -1), (key2081, -1), (key2334, 1), (key2329, 1), (key2088, 1), (key2081, 1), (key2334, -1), (key2331, -1), (key2190, 1), (key2180, 1), (key2290, -1), (key2282, -1)]

def rawRow6873 : Integer.Sparse Key := [(key2178, -2), (key2154, 1), (key2180, 1), (key2178, -2), (key2035, 1), (key2190, 1), (key2154, 1), (key2180, 1), (key2035, 1), (key2190, 1), (key2038, -2), (key2170, -2), (key2278, 2), (key2154, -1), (key2282, -1), (key2278, 2), (key2065, -1), (key2290, -1), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, 2), (key2170, 2), (key2278, -1), (key2329, -1), (key2178, 1), (key2331, 1), (key2278, -1), (key2329, -1), (key2083, 1), (key2290, 1), (key2178, 1), (key2331, 1), (key2088, -1), (key2190, -1), (key2083, 1), (key2290, 1), (key2088, -1), (key2190, -1)]

def rawRow6874 : Integer.Sparse Key := [(key2178, -2), (key2180, 1), (key2154, 1), (key2178, -2), (key2190, 1), (key2035, 1), (key2180, 1), (key2154, 1), (key2190, 1), (key2035, 1), (key2170, -2), (key2038, -2), (key2278, 2), (key2282, -1), (key2154, -1), (key2278, 2), (key2290, -1), (key2065, -1), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, 2), (key2073, 2), (key2329, -1), (key2278, -1), (key2331, 1), (key2178, 1), (key2329, -1), (key2278, -1), (key2290, 1), (key2083, 1), (key2331, 1), (key2178, 1), (key2190, -1), (key2088, -1), (key2290, 1), (key2083, 1), (key2190, -1), (key2088, -1)]

def rawRow6875 : Integer.Sparse Key := [(key2180, -2), (key2154, 1), (key2178, 1), (key2190, -2), (key2035, 1), (key2178, 1), (key2170, 1), (key2190, 1), (key2038, 1), (key2180, 1), (key2035, -2), (key2154, -2), (key2282, 2), (key2154, -1), (key2278, -1), (key2290, 2), (key2065, -1), (key2278, -1), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, 2), (key2154, 2), (key2282, -1), (key2331, -1), (key2180, 1), (key2329, 1), (key2290, -1), (key2334, -1), (key2081, 1), (key2278, 1), (key2190, 1), (key2334, 1), (key2081, -1), (key2178, -1), (key2088, 1), (key2282, 1), (key2083, -1), (key2180, -1)]

def rawRow6876 : Integer.Sparse Key := [(key2180, -2), (key2178, 1), (key2154, 1), (key2190, -2), (key2178, 1), (key2035, 1), (key2190, 1), (key2170, 1), (key2180, 1), (key2038, 1), (key2154, -2), (key2035, -2), (key2282, 2), (key2278, -1), (key2154, -1), (key2290, 2), (key2278, -1), (key2065, -1), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, 2), (key2065, 2), (key2331, -1), (key2282, -1), (key2329, 1), (key2180, 1), (key2334, -1), (key2290, -1), (key2278, 1), (key2081, 1), (key2334, 1), (key2190, 1), (key2178, -1), (key2081, -1), (key2282, 1), (key2088, 1), (key2180, -1), (key2083, -1)]

def rawRow6877 : Integer.Sparse Key := [(key2170, -2), (key2190, 1), (key2190, 1), (key2038, -2), (key2180, 1), (key2180, 1), (key2035, 1), (key2035, 1), (key2154, 1), (key2154, 1), (key2178, -2), (key2178, -2), (key2170, 2), (key2290, -1), (key2290, -1), (key2073, 2), (key2282, -1), (key2282, -1), (key2065, -1), (key2065, -1), (key2154, -1), (key2154, -1), (key2278, 2), (key2278, 2), (key2190, -1), (key2190, -1), (key2290, 1), (key2290, 1), (key2088, -1), (key2088, -1), (key2331, 1), (key2331, 1), (key2083, 1), (key2083, 1), (key2329, -1), (key2329, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1)]

def rawRow6878 : Integer.Sparse Key := [(key2190, -2), (key2170, 1), (key2190, 1), (key2180, -2), (key2038, 1), (key2180, 1), (key2154, 1), (key2178, 1), (key2035, 1), (key2178, 1), (key2035, -2), (key2154, -2), (key2290, 2), (key2170, -1), (key2290, -1), (key2282, 2), (key2073, -1), (key2282, -1), (key2154, -1), (key2278, -1), (key2065, -1), (key2278, -1), (key2065, 2), (key2154, 2), (key2290, -1), (key2334, -1), (key2190, 1), (key2334, 1), (key2282, -1), (key2331, -1), (key2088, 1), (key2282, 1), (key2180, 1), (key2329, 1), (key2083, -1), (key2180, -1), (key2081, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

def rawRow6879 : Integer.Sparse Key := [(key2190, -2), (key2190, 1), (key2170, 1), (key2180, -2), (key2180, 1), (key2038, 1), (key2178, 1), (key2154, 1), (key2178, 1), (key2035, 1), (key2154, -2), (key2035, -2), (key2290, 2), (key2290, -1), (key2170, -1), (key2282, 2), (key2282, -1), (key2073, -1), (key2278, -1), (key2154, -1), (key2278, -1), (key2065, -1), (key2154, 2), (key2065, 2), (key2334, -1), (key2290, -1), (key2334, 1), (key2190, 1), (key2331, -1), (key2282, -1), (key2282, 1), (key2088, 1), (key2329, 1), (key2180, 1), (key2180, -1), (key2083, -1), (key2278, 1), (key2081, 1), (key2178, -1), (key2081, -1)]

def rawRow6880 : Integer.Sparse Key := [(key2065, -2), (key2081, 1), (key2083, 1), (key2065, -2), (key2278, 1), (key2290, 1), (key2081, 1), (key2083, 1), (key2278, 1), (key2290, 1), (key2329, -2), (key2334, -2), (key2035, 2), (key2081, -1), (key2088, -1), (key2035, 2), (key2178, -1), (key2190, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, 2), (key2334, 2), (key2035, -1), (key2038, -1), (key2065, 1), (key2073, 1), (key2035, -1), (key2038, -1), (key2180, 1), (key2190, 1), (key2065, 1), (key2073, 1), (key2282, -1), (key2290, -1), (key2180, 1), (key2190, 1), (key2282, -1), (key2290, -1)]

def rawRow6881 : Integer.Sparse Key := [(key2065, -2), (key2083, 1), (key2081, 1), (key2065, -2), (key2290, 1), (key2278, 1), (key2083, 1), (key2081, 1), (key2290, 1), (key2278, 1), (key2334, -2), (key2329, -2), (key2035, 2), (key2088, -1), (key2081, -1), (key2035, 2), (key2190, -1), (key2178, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, 2), (key2331, 2), (key2038, -1), (key2035, -1), (key2073, 1), (key2065, 1), (key2038, -1), (key2035, -1), (key2190, 1), (key2180, 1), (key2073, 1), (key2065, 1), (key2290, -1), (key2282, -1), (key2190, 1), (key2180, 1), (key2290, -1), (key2282, -1)]

def rawRow6882 : Integer.Sparse Key := [(key2081, -2), (key2065, 1), (key2083, 1), (key2278, -2), (key2065, 1), (key2290, 1), (key2278, 1), (key2329, 1), (key2081, 1), (key2334, 1), (key2083, -2), (key2290, -2), (key2081, 2), (key2035, -1), (key2088, -1), (key2178, 2), (key2035, -1), (key2190, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, 2), (key2190, 2), (key2065, -1), (key2083, -1), (key2035, 1), (key2088, 1), (key2154, -1), (key2180, -1), (key2038, 1), (key2170, 1), (key2154, 1), (key2282, 1), (key2073, -1), (key2170, -1), (key2083, 1), (key2290, 1), (key2088, -1), (key2190, -1)]

def rawRow6883 : Integer.Sparse Key := [(key2081, -2), (key2083, 1), (key2065, 1), (key2278, -2), (key2290, 1), (key2065, 1), (key2329, 1), (key2278, 1), (key2334, 1), (key2081, 1), (key2290, -2), (key2083, -2), (key2081, 2), (key2088, -1), (key2035, -1), (key2178, 2), (key2190, -1), (key2035, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, 2), (key2088, 2), (key2083, -1), (key2065, -1), (key2088, 1), (key2035, 1), (key2180, -1), (key2154, -1), (key2170, 1), (key2038, 1), (key2282, 1), (key2154, 1), (key2170, -1), (key2073, -1), (key2290, 1), (key2083, 1), (key2190, -1), (key2088, -1)]

def rawRow6884 : Integer.Sparse Key := [(key2083, -2), (key2065, 1), (key2081, 1), (key2290, -2), (key2065, 1), (key2278, 1), (key2290, 1), (key2334, 1), (key2083, 1), (key2329, 1), (key2081, -2), (key2278, -2), (key2088, 2), (key2035, -1), (key2081, -1), (key2190, 2), (key2035, -1), (key2178, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, 2), (key2178, 2), (key2073, -1), (key2088, -1), (key2038, 1), (key2083, 1), (key2170, -1), (key2190, -1), (key2035, 1), (key2154, 1), (key2170, 1), (key2290, 1), (key2065, -1), (key2154, -1), (key2088, 1), (key2282, 1), (key2083, -1), (key2180, -1)]

def rawRow6885 : Integer.Sparse Key := [(key2083, -2), (key2081, 1), (key2065, 1), (key2290, -2), (key2278, 1), (key2065, 1), (key2334, 1), (key2290, 1), (key2329, 1), (key2083, 1), (key2278, -2), (key2081, -2), (key2088, 2), (key2081, -1), (key2035, -1), (key2190, 2), (key2178, -1), (key2035, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, 2), (key2081, 2), (key2088, -1), (key2073, -1), (key2083, 1), (key2038, 1), (key2190, -1), (key2170, -1), (key2154, 1), (key2035, 1), (key2290, 1), (key2170, 1), (key2154, -1), (key2065, -1), (key2282, 1), (key2088, 1), (key2180, -1), (key2083, -1)]

def rawRow6886 : Integer.Sparse Key := [(key2278, -2), (key2278, 1), (key2329, 1), (key2081, -2), (key2081, 1), (key2334, 1), (key2065, 1), (key2083, 1), (key2065, 1), (key2290, 1), (key2083, -2), (key2290, -2), (key2178, 2), (key2178, -1), (key2331, -1), (key2081, 2), (key2081, -1), (key2334, -1), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, 2), (key2190, 2), (key2154, -1), (key2180, -1), (key2154, 1), (key2282, 1), (key2065, -1), (key2083, -1), (key2083, 1), (key2290, 1), (key2035, 1), (key2088, 1), (key2088, -1), (key2190, -1), (key2038, 1), (key2170, 1), (key2073, -1), (key2170, -1)]

def rawRow6887 : Integer.Sparse Key := [(key2278, -2), (key2329, 1), (key2278, 1), (key2081, -2), (key2334, 1), (key2081, 1), (key2083, 1), (key2065, 1), (key2290, 1), (key2065, 1), (key2290, -2), (key2083, -2), (key2178, 2), (key2331, -1), (key2178, -1), (key2081, 2), (key2334, -1), (key2081, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, 2), (key2088, 2), (key2180, -1), (key2154, -1), (key2282, 1), (key2154, 1), (key2083, -1), (key2065, -1), (key2290, 1), (key2083, 1), (key2088, 1), (key2035, 1), (key2190, -1), (key2088, -1), (key2170, 1), (key2038, 1), (key2170, -1), (key2073, -1)]

def rawRow6888 : Integer.Sparse Key := [(key2329, -2), (key2278, 1), (key2278, 1), (key2334, -2), (key2081, 1), (key2081, 1), (key2290, 1), (key2290, 1), (key2083, 1), (key2083, 1), (key2065, -2), (key2065, -2), (key2331, 2), (key2178, -1), (key2178, -1), (key2334, 2), (key2081, -1), (key2081, -1), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, 2), (key2035, 2), (key2282, -1), (key2282, -1), (key2180, 1), (key2180, 1), (key2290, -1), (key2290, -1), (key2065, 1), (key2065, 1), (key2190, 1), (key2190, 1), (key2035, -1), (key2035, -1), (key2073, 1), (key2073, 1), (key2038, -1), (key2038, -1)]

def rawRow6889 : Integer.Sparse Key := [(key2290, -2), (key2290, 1), (key2334, 1), (key2083, -2), (key2083, 1), (key2329, 1), (key2065, 1), (key2081, 1), (key2065, 1), (key2278, 1), (key2081, -2), (key2278, -2), (key2190, 2), (key2190, -1), (key2334, -1), (key2088, 2), (key2088, -1), (key2331, -1), (key2035, -1), (key2081, -1), (key2035, -1), (key2178, -1), (key2081, 2), (key2178, 2), (key2170, -1), (key2190, -1), (key2170, 1), (key2290, 1), (key2073, -1), (key2088, -1), (key2088, 1), (key2282, 1), (key2038, 1), (key2083, 1), (key2083, -1), (key2180, -1), (key2035, 1), (key2154, 1), (key2065, -1), (key2154, -1)]

def rawRow6890 : Integer.Sparse Key := [(key2290, -2), (key2334, 1), (key2290, 1), (key2083, -2), (key2329, 1), (key2083, 1), (key2081, 1), (key2065, 1), (key2278, 1), (key2065, 1), (key2278, -2), (key2081, -2), (key2190, 2), (key2334, -1), (key2190, -1), (key2088, 2), (key2331, -1), (key2088, -1), (key2081, -1), (key2035, -1), (key2178, -1), (key2035, -1), (key2178, 2), (key2081, 2), (key2190, -1), (key2170, -1), (key2290, 1), (key2170, 1), (key2088, -1), (key2073, -1), (key2282, 1), (key2088, 1), (key2083, 1), (key2038, 1), (key2180, -1), (key2083, -1), (key2154, 1), (key2035, 1), (key2154, -1), (key2065, -1)]

def rawRow6891 : Integer.Sparse Key := [(key2334, -2), (key2290, 1), (key2290, 1), (key2329, -2), (key2083, 1), (key2083, 1), (key2278, 1), (key2278, 1), (key2081, 1), (key2081, 1), (key2065, -2), (key2065, -2), (key2334, 2), (key2190, -1), (key2190, -1), (key2331, 2), (key2088, -1), (key2088, -1), (key2178, -1), (key2178, -1), (key2081, -1), (key2081, -1), (key2035, 2), (key2035, 2), (key2290, -1), (key2290, -1), (key2190, 1), (key2190, 1), (key2282, -1), (key2282, -1), (key2073, 1), (key2073, 1), (key2180, 1), (key2180, 1), (key2038, -1), (key2038, -1), (key2065, 1), (key2065, 1), (key2035, -1), (key2035, -1)]

def rawRow6892 : Integer.Sparse Key := [(key2073, -2), (key2088, 1), (key2088, 1), (key2073, -2), (key2282, 1), (key2282, 1), (key2088, 1), (key2088, 1), (key2282, 1), (key2282, 1), (key2331, -2), (key2331, -2), (key2038, 2), (key2083, -1), (key2083, -1), (key2038, 2), (key2180, -1), (key2180, -1), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2329, 2), (key2329, 2), (key2035, -1), (key2035, -1), (key2065, 1), (key2065, 1), (key2035, -1), (key2035, -1), (key2178, 1), (key2178, 1), (key2065, 1), (key2065, 1), (key2278, -1), (key2278, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1)]

def rawRow6893 : Integer.Sparse Key := [(key2088, -2), (key2073, 1), (key2088, 1), (key2282, -2), (key2073, 1), (key2282, 1), (key2282, 1), (key2331, 1), (key2088, 1), (key2331, 1), (key2088, -2), (key2282, -2), (key2083, 2), (key2038, -1), (key2083, -1), (key2180, 2), (key2038, -1), (key2180, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2329, -1), (key2083, 2), (key2180, 2), (key2065, -1), (key2081, -1), (key2035, 1), (key2081, 1), (key2154, -1), (key2178, -1), (key2035, 1), (key2154, 1), (key2154, 1), (key2278, 1), (key2065, -1), (key2154, -1), (key2081, 1), (key2278, 1), (key2081, -1), (key2178, -1)]

def rawRow6894 : Integer.Sparse Key := [(key2088, -2), (key2088, 1), (key2073, 1), (key2282, -2), (key2282, 1), (key2073, 1), (key2331, 1), (key2282, 1), (key2331, 1), (key2088, 1), (key2282, -2), (key2088, -2), (key2083, 2), (key2083, -1), (key2038, -1), (key2180, 2), (key2180, -1), (key2038, -1), (key2329, -1), (key2180, -1), (key2329, -1), (key2083, -1), (key2180, 2), (key2083, 2), (key2081, -1), (key2065, -1), (key2081, 1), (key2035, 1), (key2178, -1), (key2154, -1), (key2154, 1), (key2035, 1), (key2278, 1), (key2154, 1), (key2154, -1), (key2065, -1), (key2278, 1), (key2081, 1), (key2178, -1), (key2081, -1)]

def rawRow6895 : Integer.Sparse Key := [(key2282, -2), (key2282, 1), (key2331, 1), (key2088, -2), (key2088, 1), (key2331, 1), (key2073, 1), (key2088, 1), (key2073, 1), (key2282, 1), (key2088, -2), (key2282, -2), (key2180, 2), (key2180, -1), (key2329, -1), (key2083, 2), (key2083, -1), (key2329, -1), (key2038, -1), (key2083, -1), (key2038, -1), (key2180, -1), (key2083, 2), (key2180, 2), (key2154, -1), (key2178, -1), (key2154, 1), (key2278, 1), (key2065, -1), (key2081, -1), (key2081, 1), (key2278, 1), (key2035, 1), (key2081, 1), (key2081, -1), (key2178, -1), (key2035, 1), (key2154, 1), (key2065, -1), (key2154, -1)]

def rawRow6896 : Integer.Sparse Key := [(key2282, -2), (key2331, 1), (key2282, 1), (key2088, -2), (key2331, 1), (key2088, 1), (key2088, 1), (key2073, 1), (key2282, 1), (key2073, 1), (key2282, -2), (key2088, -2), (key2180, 2), (key2329, -1), (key2180, -1), (key2083, 2), (key2329, -1), (key2083, -1), (key2083, -1), (key2038, -1), (key2180, -1), (key2038, -1), (key2180, 2), (key2083, 2), (key2178, -1), (key2154, -1), (key2278, 1), (key2154, 1), (key2081, -1), (key2065, -1), (key2278, 1), (key2081, 1), (key2081, 1), (key2035, 1), (key2178, -1), (key2081, -1), (key2154, 1), (key2035, 1), (key2154, -1), (key2065, -1)]

def rawRow6897 : Integer.Sparse Key := [(key2331, -2), (key2282, 1), (key2282, 1), (key2331, -2), (key2088, 1), (key2088, 1), (key2282, 1), (key2282, 1), (key2088, 1), (key2088, 1), (key2073, -2), (key2073, -2), (key2329, 2), (key2180, -1), (key2180, -1), (key2329, 2), (key2083, -1), (key2083, -1), (key2180, -1), (key2180, -1), (key2083, -1), (key2083, -1), (key2038, 2), (key2038, 2), (key2278, -1), (key2278, -1), (key2178, 1), (key2178, 1), (key2278, -1), (key2278, -1), (key2065, 1), (key2065, 1), (key2178, 1), (key2178, 1), (key2035, -1), (key2035, -1), (key2065, 1), (key2065, 1), (key2035, -1), (key2035, -1)]

def rawRow6898 : Integer.Sparse Key := [(key725, -1), (key726, -1), (key726, 2), (key728, -1), (key729, -1), (key728, 2), (key735, 2), (key729, -1), (key735, -1), (key739, 2), (key739, -1), (key744, -1), (key725, 1), (key726, 1), (key726, -2), (key794, 1), (key795, 1), (key794, -2), (key813, -2), (key795, 1), (key813, 1), (key819, -2), (key819, 1), (key826, 1), (key728, -1), (key735, -1), (key729, 1), (key735, 1), (key794, 1), (key813, 1), (key795, -1), (key813, -1), (key864, -1), (key869, -1), (key864, 1), (key878, 1), (key899, 1), (key903, 1), (key899, -1), (key909, -1)]

def rawRow6899 : Integer.Sparse Key := [(key726, -1), (key725, -1), (key726, 2), (key729, -1), (key728, -1), (key735, 2), (key728, 2), (key735, -1), (key729, -1), (key739, 2), (key744, -1), (key739, -1), (key726, 1), (key725, 1), (key726, -2), (key795, 1), (key794, 1), (key813, -2), (key794, -2), (key813, 1), (key795, 1), (key819, -2), (key826, 1), (key819, 1), (key735, -1), (key728, -1), (key735, 1), (key729, 1), (key813, 1), (key794, 1), (key813, -1), (key795, -1), (key869, -1), (key864, -1), (key878, 1), (key864, 1), (key903, 1), (key899, 1), (key909, -1), (key899, -1)]

def rawRow6900 : Integer.Sparse Key := [(key726, -1), (key726, -1), (key725, 2), (key735, -1), (key735, -1), (key729, 2), (key729, 2), (key728, -1), (key728, -1), (key744, 2), (key739, -1), (key739, -1), (key726, 1), (key726, 1), (key725, -2), (key813, 1), (key813, 1), (key795, -2), (key795, -2), (key794, 1), (key794, 1), (key826, -2), (key819, 1), (key819, 1), (key729, -1), (key729, -1), (key728, 1), (key728, 1), (key795, 1), (key795, 1), (key794, -1), (key794, -1), (key878, -1), (key878, -1), (key869, 1), (key869, 1), (key909, 1), (key909, 1), (key903, -1), (key903, -1)]

def rawRow6901 : Integer.Sparse Key := [(key728, -1), (key729, -1), (key739, 2), (key725, -1), (key726, -1), (key728, 2), (key735, 2), (key739, -1), (key744, -1), (key726, 2), (key729, -1), (key735, -1), (key794, 1), (key795, 1), (key819, -2), (key725, 1), (key726, 1), (key794, -2), (key813, -2), (key819, 1), (key826, 1), (key726, -2), (key795, 1), (key813, 1), (key864, -1), (key869, -1), (key899, 1), (key903, 1), (key864, 1), (key878, 1), (key899, -1), (key909, -1), (key728, -1), (key735, -1), (key794, 1), (key813, 1), (key729, 1), (key735, 1), (key795, -1), (key813, -1)]

def rawRow6902 : Integer.Sparse Key := [(key729, -1), (key728, -1), (key739, 2), (key726, -1), (key725, -1), (key735, 2), (key728, 2), (key744, -1), (key739, -1), (key726, 2), (key735, -1), (key729, -1), (key795, 1), (key794, 1), (key819, -2), (key726, 1), (key725, 1), (key813, -2), (key794, -2), (key826, 1), (key819, 1), (key726, -2), (key813, 1), (key795, 1), (key869, -1), (key864, -1), (key903, 1), (key899, 1), (key878, 1), (key864, 1), (key909, -1), (key899, -1), (key735, -1), (key728, -1), (key813, 1), (key794, 1), (key735, 1), (key729, 1), (key813, -1), (key795, -1)]

def rawRow6903 : Integer.Sparse Key := [(key728, -1), (key739, -1), (key729, 2), (key728, -1), (key739, -1), (key725, 2), (key744, 2), (key726, -1), (key735, -1), (key729, 2), (key726, -1), (key735, -1), (key794, 1), (key819, 1), (key795, -2), (key794, 1), (key819, 1), (key725, -2), (key826, -2), (key726, 1), (key813, 1), (key795, -2), (key726, 1), (key813, 1), (key794, -1), (key903, -1), (key795, 1), (key869, 1), (key728, 1), (key909, 1), (key729, -1), (key878, -1), (key794, -1), (key903, -1), (key728, 1), (key909, 1), (key795, 1), (key869, 1), (key729, -1), (key878, -1)]

def rawRow6904 : Integer.Sparse Key := [(key739, -1), (key728, -1), (key729, 2), (key739, -1), (key728, -1), (key744, 2), (key725, 2), (key735, -1), (key726, -1), (key729, 2), (key735, -1), (key726, -1), (key819, 1), (key794, 1), (key795, -2), (key819, 1), (key794, 1), (key826, -2), (key725, -2), (key813, 1), (key726, 1), (key795, -2), (key813, 1), (key726, 1), (key903, -1), (key794, -1), (key869, 1), (key795, 1), (key909, 1), (key728, 1), (key878, -1), (key729, -1), (key903, -1), (key794, -1), (key909, 1), (key728, 1), (key869, 1), (key795, 1), (key878, -1), (key729, -1)]

def rawRow6905 : Integer.Sparse Key := [(key729, -1), (key739, -1), (key728, 2), (key735, -1), (key744, -1), (key726, 2), (key739, 2), (key725, -1), (key728, -1), (key735, 2), (key726, -1), (key729, -1), (key795, 1), (key819, 1), (key794, -2), (key813, 1), (key826, 1), (key726, -2), (key819, -2), (key725, 1), (key794, 1), (key813, -2), (key726, 1), (key795, 1), (key795, -1), (key899, -1), (key794, 1), (key864, 1), (key729, 1), (key899, 1), (key728, -1), (key864, -1), (key813, -1), (key909, -1), (key735, 1), (key903, 1), (key813, 1), (key878, 1), (key735, -1), (key869, -1)]

def rawRow6906 : Integer.Sparse Key := [(key739, -1), (key729, -1), (key728, 2), (key744, -1), (key735, -1), (key739, 2), (key726, 2), (key728, -1), (key725, -1), (key735, 2), (key729, -1), (key726, -1), (key819, 1), (key795, 1), (key794, -2), (key826, 1), (key813, 1), (key819, -2), (key726, -2), (key794, 1), (key725, 1), (key813, -2), (key795, 1), (key726, 1), (key899, -1), (key795, -1), (key864, 1), (key794, 1), (key899, 1), (key729, 1), (key864, -1), (key728, -1), (key909, -1), (key813, -1), (key903, 1), (key735, 1), (key878, 1), (key813, 1), (key869, -1), (key735, -1)]

def rawRow6907 : Integer.Sparse Key := [(key735, -1), (key735, -1), (key744, 2), (key726, -1), (key726, -1), (key729, 2), (key729, 2), (key739, -1), (key739, -1), (key725, 2), (key728, -1), (key728, -1), (key813, 1), (key813, 1), (key826, -2), (key726, 1), (key726, 1), (key795, -2), (key795, -2), (key819, 1), (key819, 1), (key725, -2), (key794, 1), (key794, 1), (key878, -1), (key878, -1), (key909, 1), (key909, 1), (key869, 1), (key869, 1), (key903, -1), (key903, -1), (key729, -1), (key729, -1), (key795, 1), (key795, 1), (key728, 1), (key728, 1), (key794, -1), (key794, -1)]

def rawRow6908 : Integer.Sparse Key := [(key735, -1), (key744, -1), (key735, 2), (key729, -1), (key739, -1), (key726, 2), (key739, 2), (key726, -1), (key729, -1), (key728, 2), (key725, -1), (key728, -1), (key813, 1), (key826, 1), (key813, -2), (key795, 1), (key819, 1), (key726, -2), (key819, -2), (key726, 1), (key795, 1), (key794, -2), (key725, 1), (key794, 1), (key813, -1), (key909, -1), (key813, 1), (key878, 1), (key735, 1), (key903, 1), (key735, -1), (key869, -1), (key795, -1), (key899, -1), (key729, 1), (key899, 1), (key794, 1), (key864, 1), (key728, -1), (key864, -1)]

def rawRow6909 : Integer.Sparse Key := [(key744, -1), (key735, -1), (key735, 2), (key739, -1), (key729, -1), (key739, 2), (key726, 2), (key729, -1), (key726, -1), (key728, 2), (key728, -1), (key725, -1), (key826, 1), (key813, 1), (key813, -2), (key819, 1), (key795, 1), (key819, -2), (key726, -2), (key795, 1), (key726, 1), (key794, -2), (key794, 1), (key725, 1), (key909, -1), (key813, -1), (key878, 1), (key813, 1), (key903, 1), (key735, 1), (key869, -1), (key735, -1), (key899, -1), (key795, -1), (key899, 1), (key729, 1), (key864, 1), (key794, 1), (key864, -1), (key728, -1)]

def rawRow6910 : Integer.Sparse Key := [(key794, -1), (key795, -1), (key819, 2), (key794, -1), (key795, -1), (key864, 2), (key869, 2), (key899, -1), (key903, -1), (key819, 2), (key899, -1), (key903, -1), (key728, 1), (key729, 1), (key739, -2), (key728, 1), (key729, 1), (key864, -2), (key878, -2), (key899, 1), (key909, 1), (key739, -2), (key899, 1), (key909, 1), (key728, -1), (key735, -1), (key739, 1), (key744, 1), (key794, 1), (key813, 1), (key819, -1), (key826, -1), (key728, -1), (key735, -1), (key794, 1), (key813, 1), (key739, 1), (key744, 1), (key819, -1), (key826, -1)]

def rawRow6911 : Integer.Sparse Key := [(key795, -1), (key794, -1), (key819, 2), (key795, -1), (key794, -1), (key869, 2), (key864, 2), (key903, -1), (key899, -1), (key819, 2), (key903, -1), (key899, -1), (key729, 1), (key728, 1), (key739, -2), (key729, 1), (key728, 1), (key878, -2), (key864, -2), (key909, 1), (key899, 1), (key739, -2), (key909, 1), (key899, 1), (key735, -1), (key728, -1), (key744, 1), (key739, 1), (key813, 1), (key794, 1), (key826, -1), (key819, -1), (key735, -1), (key728, -1), (key813, 1), (key794, 1), (key744, 1), (key739, 1), (key826, -1), (key819, -1)]

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

def rawRow6912 : Integer.Sparse Key := [(key794, -1), (key819, -1), (key795, 2), (key864, -1), (key899, -1), (key794, 2), (key903, 2), (key795, -1), (key869, -1), (key899, 2), (key819, -1), (key903, -1), (key728, 1), (key739, 1), (key729, -2), (key864, 1), (key899, 1), (key728, -2), (key909, -2), (key729, 1), (key878, 1), (key899, -2), (key739, 1), (key909, 1), (key725, -1), (key744, -1), (key726, 1), (key735, 1), (key725, 1), (key826, 1), (key726, -1), (key813, -1), (key794, -1), (key903, -1), (key728, 1), (key909, 1), (key819, 1), (key903, 1), (key739, -1), (key909, -1)]

def rawRow6913 : Integer.Sparse Key := [(key819, -1), (key794, -1), (key795, 2), (key899, -1), (key864, -1), (key903, 2), (key794, 2), (key869, -1), (key795, -1), (key899, 2), (key903, -1), (key819, -1), (key739, 1), (key728, 1), (key729, -2), (key899, 1), (key864, 1), (key909, -2), (key728, -2), (key878, 1), (key729, 1), (key899, -2), (key909, 1), (key739, 1), (key744, -1), (key725, -1), (key735, 1), (key726, 1), (key826, 1), (key725, 1), (key813, -1), (key726, -1), (key903, -1), (key794, -1), (key909, 1), (key728, 1), (key903, 1), (key819, 1), (key909, -1), (key739, -1)]

def rawRow6914 : Integer.Sparse Key := [(key795, -1), (key819, -1), (key794, 2), (key869, -1), (key903, -1), (key795, 2), (key899, 2), (key794, -1), (key864, -1), (key903, 2), (key819, -1), (key899, -1), (key729, 1), (key739, 1), (key728, -2), (key878, 1), (key909, 1), (key729, -2), (key899, -2), (key728, 1), (key864, 1), (key909, -2), (key739, 1), (key899, 1), (key726, -1), (key739, -1), (key725, 1), (key728, 1), (key726, 1), (key819, 1), (key725, -1), (key794, -1), (key813, -1), (key909, -1), (key735, 1), (key903, 1), (key826, 1), (key909, 1), (key744, -1), (key903, -1)]

def rawRow6915 : Integer.Sparse Key := [(key819, -1), (key795, -1), (key794, 2), (key903, -1), (key869, -1), (key899, 2), (key795, 2), (key864, -1), (key794, -1), (key903, 2), (key899, -1), (key819, -1), (key739, 1), (key729, 1), (key728, -2), (key909, 1), (key878, 1), (key899, -2), (key729, -2), (key864, 1), (key728, 1), (key909, -2), (key899, 1), (key739, 1), (key739, -1), (key726, -1), (key728, 1), (key725, 1), (key819, 1), (key726, 1), (key794, -1), (key725, -1), (key909, -1), (key813, -1), (key903, 1), (key735, 1), (key909, 1), (key826, 1), (key903, -1), (key744, -1)]

def rawRow6916 : Integer.Sparse Key := [(key864, -1), (key899, -1), (key899, 2), (key794, -1), (key819, -1), (key794, 2), (key903, 2), (key819, -1), (key903, -1), (key795, 2), (key795, -1), (key869, -1), (key864, 1), (key899, 1), (key899, -2), (key728, 1), (key739, 1), (key728, -2), (key909, -2), (key739, 1), (key909, 1), (key729, -2), (key729, 1), (key878, 1), (key794, -1), (key903, -1), (key819, 1), (key903, 1), (key728, 1), (key909, 1), (key739, -1), (key909, -1), (key725, -1), (key744, -1), (key725, 1), (key826, 1), (key726, 1), (key735, 1), (key726, -1), (key813, -1)]

def rawRow6917 : Integer.Sparse Key := [(key899, -1), (key864, -1), (key899, 2), (key819, -1), (key794, -1), (key903, 2), (key794, 2), (key903, -1), (key819, -1), (key795, 2), (key869, -1), (key795, -1), (key899, 1), (key864, 1), (key899, -2), (key739, 1), (key728, 1), (key909, -2), (key728, -2), (key909, 1), (key739, 1), (key729, -2), (key878, 1), (key729, 1), (key903, -1), (key794, -1), (key903, 1), (key819, 1), (key909, 1), (key728, 1), (key909, -1), (key739, -1), (key744, -1), (key725, -1), (key826, 1), (key725, 1), (key735, 1), (key726, 1), (key813, -1), (key726, -1)]

def rawRow6918 : Integer.Sparse Key := [(key899, -1), (key899, -1), (key864, 2), (key903, -1), (key903, -1), (key819, 2), (key819, 2), (key794, -1), (key794, -1), (key869, 2), (key795, -1), (key795, -1), (key899, 1), (key899, 1), (key864, -2), (key909, 1), (key909, 1), (key739, -2), (key739, -2), (key728, 1), (key728, 1), (key878, -2), (key729, 1), (key729, 1), (key819, -1), (key819, -1), (key794, 1), (key794, 1), (key739, 1), (key739, 1), (key728, -1), (key728, -1), (key826, -1), (key826, -1), (key744, 1), (key744, 1), (key813, 1), (key813, 1), (key735, -1), (key735, -1)]

def rawRow6919 : Integer.Sparse Key := [(key869, -1), (key903, -1), (key903, 2), (key795, -1), (key819, -1), (key795, 2), (key899, 2), (key819, -1), (key899, -1), (key794, 2), (key794, -1), (key864, -1), (key878, 1), (key909, 1), (key909, -2), (key729, 1), (key739, 1), (key729, -2), (key899, -2), (key739, 1), (key899, 1), (key728, -2), (key728, 1), (key864, 1), (key813, -1), (key909, -1), (key826, 1), (key909, 1), (key735, 1), (key903, 1), (key744, -1), (key903, -1), (key726, -1), (key739, -1), (key726, 1), (key819, 1), (key725, 1), (key728, 1), (key725, -1), (key794, -1)]

def rawRow6920 : Integer.Sparse Key := [(key903, -1), (key869, -1), (key903, 2), (key819, -1), (key795, -1), (key899, 2), (key795, 2), (key899, -1), (key819, -1), (key794, 2), (key864, -1), (key794, -1), (key909, 1), (key878, 1), (key909, -2), (key739, 1), (key729, 1), (key899, -2), (key729, -2), (key899, 1), (key739, 1), (key728, -2), (key864, 1), (key728, 1), (key909, -1), (key813, -1), (key909, 1), (key826, 1), (key903, 1), (key735, 1), (key903, -1), (key744, -1), (key739, -1), (key726, -1), (key819, 1), (key726, 1), (key728, 1), (key725, 1), (key794, -1), (key725, -1)]

def rawRow6921 : Integer.Sparse Key := [(key903, -1), (key903, -1), (key869, 2), (key899, -1), (key899, -1), (key819, 2), (key819, 2), (key795, -1), (key795, -1), (key864, 2), (key794, -1), (key794, -1), (key909, 1), (key909, 1), (key878, -2), (key899, 1), (key899, 1), (key739, -2), (key739, -2), (key729, 1), (key729, 1), (key864, -2), (key728, 1), (key728, 1), (key826, -1), (key826, -1), (key813, 1), (key813, 1), (key744, 1), (key744, 1), (key735, -1), (key735, -1), (key819, -1), (key819, -1), (key739, 1), (key739, 1), (key794, 1), (key794, 1), (key728, -1), (key728, -1)]

def rawRow6922 : Integer.Sparse Key := [(key813, -1), (key813, -1), (key826, 2), (key813, -1), (key813, -1), (key878, 2), (key878, 2), (key909, -1), (key909, -1), (key826, 2), (key909, -1), (key909, -1), (key735, 1), (key735, 1), (key744, -2), (key735, 1), (key735, 1), (key869, -2), (key869, -2), (key903, 1), (key903, 1), (key744, -2), (key903, 1), (key903, 1), (key729, -1), (key729, -1), (key739, 1), (key739, 1), (key795, 1), (key795, 1), (key819, -1), (key819, -1), (key729, -1), (key729, -1), (key795, 1), (key795, 1), (key739, 1), (key739, 1), (key819, -1), (key819, -1)]

def rawRow6923 : Integer.Sparse Key := [(key813, -1), (key826, -1), (key813, 2), (key878, -1), (key909, -1), (key813, 2), (key909, 2), (key813, -1), (key878, -1), (key909, 2), (key826, -1), (key909, -1), (key735, 1), (key744, 1), (key735, -2), (key869, 1), (key903, 1), (key735, -2), (key903, -2), (key735, 1), (key869, 1), (key903, -2), (key744, 1), (key903, 1), (key726, -1), (key739, -1), (key726, 1), (key729, 1), (key726, 1), (key819, 1), (key726, -1), (key795, -1), (key795, -1), (key899, -1), (key729, 1), (key899, 1), (key819, 1), (key899, 1), (key739, -1), (key899, -1)]

def rawRow6924 : Integer.Sparse Key := [(key826, -1), (key813, -1), (key813, 2), (key909, -1), (key878, -1), (key909, 2), (key813, 2), (key878, -1), (key813, -1), (key909, 2), (key909, -1), (key826, -1), (key744, 1), (key735, 1), (key735, -2), (key903, 1), (key869, 1), (key903, -2), (key735, -2), (key869, 1), (key735, 1), (key903, -2), (key903, 1), (key744, 1), (key739, -1), (key726, -1), (key729, 1), (key726, 1), (key819, 1), (key726, 1), (key795, -1), (key726, -1), (key899, -1), (key795, -1), (key899, 1), (key729, 1), (key899, 1), (key819, 1), (key899, -1), (key739, -1)]

def rawRow6925 : Integer.Sparse Key := [(key878, -1), (key909, -1), (key909, 2), (key813, -1), (key826, -1), (key813, 2), (key909, 2), (key826, -1), (key909, -1), (key813, 2), (key813, -1), (key878, -1), (key869, 1), (key903, 1), (key903, -2), (key735, 1), (key744, 1), (key735, -2), (key903, -2), (key744, 1), (key903, 1), (key735, -2), (key735, 1), (key869, 1), (key795, -1), (key899, -1), (key819, 1), (key899, 1), (key729, 1), (key899, 1), (key739, -1), (key899, -1), (key726, -1), (key739, -1), (key726, 1), (key819, 1), (key726, 1), (key729, 1), (key726, -1), (key795, -1)]

def rawRow6926 : Integer.Sparse Key := [(key909, -1), (key878, -1), (key909, 2), (key826, -1), (key813, -1), (key909, 2), (key813, 2), (key909, -1), (key826, -1), (key813, 2), (key878, -1), (key813, -1), (key903, 1), (key869, 1), (key903, -2), (key744, 1), (key735, 1), (key903, -2), (key735, -2), (key903, 1), (key744, 1), (key735, -2), (key869, 1), (key735, 1), (key899, -1), (key795, -1), (key899, 1), (key819, 1), (key899, 1), (key729, 1), (key899, -1), (key739, -1), (key739, -1), (key726, -1), (key819, 1), (key726, 1), (key729, 1), (key726, 1), (key795, -1), (key726, -1)]

def rawRow6927 : Integer.Sparse Key := [(key909, -1), (key909, -1), (key878, 2), (key909, -1), (key909, -1), (key826, 2), (key826, 2), (key813, -1), (key813, -1), (key878, 2), (key813, -1), (key813, -1), (key903, 1), (key903, 1), (key869, -2), (key903, 1), (key903, 1), (key744, -2), (key744, -2), (key735, 1), (key735, 1), (key869, -2), (key735, 1), (key735, 1), (key819, -1), (key819, -1), (key795, 1), (key795, 1), (key739, 1), (key739, 1), (key729, -1), (key729, -1), (key819, -1), (key819, -1), (key739, 1), (key739, 1), (key795, 1), (key795, 1), (key729, -1), (key729, -1)]

def rawRow6928 : Integer.Sparse Key := [(key2031, 1), (key2036, 1), (key2036, -2), (key2150, 1), (key2155, 1), (key2150, -2), (key2168, -2), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, 1), (key2201, 1), (key2061, -1), (key2066, -1), (key2066, 1), (key2071, 1), (key2150, -1), (key2155, -1), (key2150, 1), (key2168, 1), (key2243, 1), (key2255, 1), (key2248, -1), (key2255, -1), (key2304, 1), (key2306, 1), (key2306, -1), (key2311, -1), (key2093, 2), (key2093, -1), (key2096, -1), (key2195, 2), (key2195, -1), (key2201, -1), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, 2), (key2311, 2)]

def rawRow6929 : Integer.Sparse Key := [(key2036, 1), (key2031, 1), (key2036, -2), (key2155, 1), (key2150, 1), (key2168, -2), (key2150, -2), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, 1), (key2195, 1), (key2066, -1), (key2061, -1), (key2071, 1), (key2066, 1), (key2155, -1), (key2150, -1), (key2168, 1), (key2150, 1), (key2255, 1), (key2243, 1), (key2255, -1), (key2248, -1), (key2306, 1), (key2304, 1), (key2311, -1), (key2306, -1), (key2093, 2), (key2096, -1), (key2093, -1), (key2195, 2), (key2201, -1), (key2195, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, 2), (key2306, 2)]

def rawRow6930 : Integer.Sparse Key := [(key2036, 1), (key2036, 1), (key2031, -2), (key2168, 1), (key2168, 1), (key2155, -2), (key2155, -2), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, 1), (key2195, 1), (key2071, -1), (key2071, -1), (key2061, 1), (key2061, 1), (key2168, -1), (key2168, -1), (key2155, 1), (key2155, 1), (key2248, 1), (key2248, 1), (key2243, -1), (key2243, -1), (key2311, 1), (key2311, 1), (key2304, -1), (key2304, -1), (key2096, 2), (key2093, -1), (key2093, -1), (key2201, 2), (key2195, -1), (key2195, -1), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, 2), (key2304, 2)]

def rawRow6931 : Integer.Sparse Key := [(key2150, 1), (key2155, 1), (key2195, -2), (key2031, 1), (key2036, 1), (key2150, -2), (key2168, -2), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, 1), (key2168, 1), (key2150, -1), (key2155, -1), (key2304, 1), (key2306, 1), (key2061, -1), (key2066, -1), (key2243, 1), (key2255, 1), (key2150, 1), (key2168, 1), (key2306, -1), (key2311, -1), (key2066, 1), (key2071, 1), (key2248, -1), (key2255, -1), (key2195, 2), (key2304, -1), (key2306, -1), (key2093, 2), (key2304, -1), (key2311, -1), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, 2), (key2311, 2)]

def rawRow6932 : Integer.Sparse Key := [(key2155, 1), (key2150, 1), (key2195, -2), (key2036, 1), (key2031, 1), (key2168, -2), (key2150, -2), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, 1), (key2155, 1), (key2155, -1), (key2150, -1), (key2306, 1), (key2304, 1), (key2066, -1), (key2061, -1), (key2255, 1), (key2243, 1), (key2168, 1), (key2150, 1), (key2311, -1), (key2306, -1), (key2071, 1), (key2066, 1), (key2255, -1), (key2248, -1), (key2195, 2), (key2306, -1), (key2304, -1), (key2093, 2), (key2311, -1), (key2304, -1), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, 2), (key2306, 2)]

def rawRow6933 : Integer.Sparse Key := [(key2150, 1), (key2195, 1), (key2155, -2), (key2150, 1), (key2195, 1), (key2031, -2), (key2201, -2), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, 1), (key2168, 1), (key2243, -1), (key2304, -1), (key2155, 1), (key2248, 1), (key2243, -1), (key2304, -1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2071, -1), (key2168, -1), (key2155, 1), (key2248, 1), (key2071, -1), (key2168, -1), (key2304, 2), (key2195, -1), (key2306, -1), (key2304, 2), (key2093, -1), (key2311, -1), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, 2), (key2201, 2)]

def rawRow6934 : Integer.Sparse Key := [(key2195, 1), (key2150, 1), (key2155, -2), (key2195, 1), (key2150, 1), (key2201, -2), (key2031, -2), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, 1), (key2036, 1), (key2304, -1), (key2243, -1), (key2248, 1), (key2155, 1), (key2304, -1), (key2243, -1), (key2311, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2168, -1), (key2071, -1), (key2248, 1), (key2155, 1), (key2168, -1), (key2071, -1), (key2304, 2), (key2306, -1), (key2195, -1), (key2304, 2), (key2311, -1), (key2093, -1), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, 2), (key2096, 2)]

def rawRow6935 : Integer.Sparse Key := [(key2155, 1), (key2195, 1), (key2150, -2), (key2168, 1), (key2201, 1), (key2036, -2), (key2195, -2), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, 1), (key2155, 1), (key2248, -1), (key2306, -1), (key2150, 1), (key2243, 1), (key2255, -1), (key2311, -1), (key2066, 1), (key2304, 1), (key2071, 1), (key2306, 1), (key2061, -1), (key2150, -1), (key2168, 1), (key2255, 1), (key2066, -1), (key2155, -1), (key2306, 2), (key2195, -1), (key2304, -1), (key2311, 2), (key2093, -1), (key2304, -1), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, 2), (key2195, 2)]

def rawRow6936 : Integer.Sparse Key := [(key2195, 1), (key2155, 1), (key2150, -2), (key2201, 1), (key2168, 1), (key2195, -2), (key2036, -2), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, 1), (key2036, 1), (key2306, -1), (key2248, -1), (key2243, 1), (key2150, 1), (key2311, -1), (key2255, -1), (key2304, 1), (key2066, 1), (key2306, 1), (key2071, 1), (key2150, -1), (key2061, -1), (key2255, 1), (key2168, 1), (key2155, -1), (key2066, -1), (key2306, 2), (key2304, -1), (key2195, -1), (key2311, 2), (key2304, -1), (key2093, -1), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, 2), (key2093, 2)]

def rawRow6937 : Integer.Sparse Key := [(key2168, 1), (key2168, 1), (key2201, -2), (key2036, 1), (key2036, 1), (key2155, -2), (key2155, -2), (key2195, 1), (key2195, 1), (key2031, -2), (key2150, 1), (key2150, 1), (key2168, -1), (key2168, -1), (key2311, 1), (key2311, 1), (key2071, -1), (key2071, -1), (key2248, 1), (key2248, 1), (key2155, 1), (key2155, 1), (key2304, -1), (key2304, -1), (key2061, 1), (key2061, 1), (key2243, -1), (key2243, -1), (key2201, 2), (key2311, -1), (key2311, -1), (key2096, 2), (key2306, -1), (key2306, -1), (key2093, -1), (key2093, -1), (key2195, -1), (key2195, -1), (key2304, 2), (key2304, 2)]

def rawRow6938 : Integer.Sparse Key := [(key2168, 1), (key2201, 1), (key2168, -2), (key2155, 1), (key2195, 1), (key2036, -2), (key2195, -2), (key2036, 1), (key2155, 1), (key2150, -2), (key2031, 1), (key2150, 1), (key2255, -1), (key2311, -1), (key2168, 1), (key2255, 1), (key2248, -1), (key2306, -1), (key2071, 1), (key2306, 1), (key2066, 1), (key2304, 1), (key2066, -1), (key2155, -1), (key2150, 1), (key2243, 1), (key2061, -1), (key2150, -1), (key2311, 2), (key2201, -1), (key2311, -1), (key2306, 2), (key2096, -1), (key2306, -1), (key2195, -1), (key2304, -1), (key2093, -1), (key2304, -1), (key2093, 2), (key2195, 2)]

def rawRow6939 : Integer.Sparse Key := [(key2201, 1), (key2168, 1), (key2168, -2), (key2195, 1), (key2155, 1), (key2195, -2), (key2036, -2), (key2155, 1), (key2036, 1), (key2150, -2), (key2150, 1), (key2031, 1), (key2311, -1), (key2255, -1), (key2255, 1), (key2168, 1), (key2306, -1), (key2248, -1), (key2306, 1), (key2071, 1), (key2304, 1), (key2066, 1), (key2155, -1), (key2066, -1), (key2243, 1), (key2150, 1), (key2150, -1), (key2061, -1), (key2311, 2), (key2311, -1), (key2201, -1), (key2306, 2), (key2306, -1), (key2096, -1), (key2304, -1), (key2195, -1), (key2304, -1), (key2093, -1), (key2195, 2), (key2093, 2)]

def rawRow6940 : Integer.Sparse Key := [(key2061, 1), (key2066, 1), (key2093, -2), (key2061, 1), (key2066, 1), (key2243, -2), (key2255, -2), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, 1), (key2311, 1), (key2031, -1), (key2036, -1), (key2093, 1), (key2096, 1), (key2031, -1), (key2036, -1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2306, -1), (key2311, -1), (key2093, 1), (key2096, 1), (key2306, -1), (key2311, -1), (key2036, 2), (key2066, -1), (key2071, -1), (key2036, 2), (key2155, -1), (key2168, -1), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, 2), (key2255, 2)]

def rawRow6941 : Integer.Sparse Key := [(key2066, 1), (key2061, 1), (key2093, -2), (key2066, 1), (key2061, 1), (key2255, -2), (key2243, -2), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, 1), (key2304, 1), (key2036, -1), (key2031, -1), (key2096, 1), (key2093, 1), (key2036, -1), (key2031, -1), (key2168, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2311, -1), (key2306, -1), (key2096, 1), (key2093, 1), (key2311, -1), (key2306, -1), (key2036, 2), (key2071, -1), (key2066, -1), (key2036, 2), (key2168, -1), (key2155, -1), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, 2), (key2248, 2)]

def rawRow6942 : Integer.Sparse Key := [(key2061, 1), (key2093, 1), (key2066, -2), (key2243, 1), (key2304, 1), (key2061, -2), (key2311, -2), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, 1), (key2311, 1), (key2061, -1), (key2093, -1), (key2036, 1), (key2071, 1), (key2150, -1), (key2195, -1), (key2031, 1), (key2201, 1), (key2061, 1), (key2311, 1), (key2071, -1), (key2168, -1), (key2195, 1), (key2306, 1), (key2096, -1), (key2201, -1), (key2066, 2), (key2036, -1), (key2071, -1), (key2155, 2), (key2036, -1), (key2168, -1), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, 2), (key2168, 2)]

def rawRow6943 : Integer.Sparse Key := [(key2093, 1), (key2061, 1), (key2066, -2), (key2304, 1), (key2243, 1), (key2311, -2), (key2061, -2), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, 1), (key2093, 1), (key2093, -1), (key2061, -1), (key2071, 1), (key2036, 1), (key2195, -1), (key2150, -1), (key2201, 1), (key2031, 1), (key2311, 1), (key2061, 1), (key2168, -1), (key2071, -1), (key2306, 1), (key2195, 1), (key2201, -1), (key2096, -1), (key2066, 2), (key2071, -1), (key2036, -1), (key2155, 2), (key2168, -1), (key2036, -1), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, 2), (key2071, 2)]

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

def rawRow7447 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key989, 6), (key1102, 6), (key1102, 6)]

end MUB6.Certificate.GramRows

end OAI
end


