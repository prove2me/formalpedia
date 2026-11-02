-- Prove2me | Definitions.Def_OAIQ106D165
-- name    : OAIQ106D165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:32:06.355529+00:00
-- url     : https://prove2.me/theorems/6bbef3c5-ec79-4c14-9a22-772715ef9b7f
-- title:
--   Definitions bundle OAIQ106D165 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 487 declarations of OpenAI's Lean: 487 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow17841`, `OAI.MUB6.Certificate.GramRows.rawRow17842`, `OAI.MUB6.Certificate.GramRows.rawRow17843`, `OAI.MUB6.Certificate.GramRows.rawRow17844`, `OAI.MUB6.Certificate.GramRows.rawRow17845`, `OAI.MUB6.Certificate.GramRows.rawRow17846`, `OAI.MUB6.Certificate.GramRows.rawRow17847`, `OAI.MUB6.Certificate.GramRows.rawRow17848`, `OAI.MUB6.Certificate.GramRows.rawRow17849`, `OAI.MUB6.Certificate.GramRows.rawRow1785`, `OAI.MUB6.Certificate.GramRows.rawRow17850`, `OAI.MUB6.Certificate.GramRows.rawRow17851`, `OAI.MUB6.Certificate.GramRows.rawRow17852`, `OAI.MUB6.Certificate.GramRows.rawRow17853`, `OAI.MUB6.Certificate.GramRows.rawRow17854`, `OAI.MUB6.Certificate.GramRows.rawRow17855`, `OAI.MUB6.Certificate.GramRows.rawRow17856`, `OAI.MUB6.Certificate.GramRows.rawRow17857`, `OAI.MUB6.Certificate.GramRows.rawRow17858`, `OAI.MUB6.Certificate.GramRows.rawRow17859`, `OAI.MUB6.Certificate.GramRows.rawRow1786`, `OAI.MUB6.Certificate.GramRows.rawRow17860`, `OAI.MUB6.Certificate.GramRows.rawRow17861`, `OAI.MUB6.Certificate.GramRows.rawRow17862`, `OAI.MUB6.Certificate.GramRows.rawRow17863`, `OAI.MUB6.Certificate.GramRows.rawRow17864`, `OAI.MUB6.Certificate.GramRows.rawRow17865`, `OAI.MUB6.Certificate.GramRows.rawRow17866`, `OAI.MUB6.Certificate.GramRows.rawRow17867`, `OAI.MUB6.Certificate.GramRows.rawRow17868`, `OAI.MUB6.Certificate.GramRows.rawRow17869`, `OAI.MUB6.Certificate.GramRows.rawRow1787`, `OAI.MUB6.Certificate.GramRows.rawRow17870`, `OAI.MUB6.Certificate.GramRows.rawRow17871`, `OAI.MUB6.Certificate.GramRows.rawRow17872`, `OAI.MUB6.Certificate.GramRows.rawRow17873`, `OAI.MUB6.Certificate.GramRows.rawRow17874`, `OAI.MUB6.Certificate.GramRows.rawRow17875`, `OAI.MUB6.Certificate.GramRows.rawRow17876`, `OAI.MUB6.Certificate.GramRows.rawRow17877` and 447 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block163`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block163.lean), [`MutuallyUnbiased_GramRows_Block164`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block164.lean), [`MutuallyUnbiased_GramRows_Block165`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block165.lean), [`MutuallyUnbiased_GramRows_Block166`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block166.lean), [`MutuallyUnbiased_GramRows_Block168`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean), [`MutuallyUnbiased_GramRows_Block37`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block37.lean), [`MutuallyUnbiased_GramRows_Block38`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block38.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17841 : Integer.Sparse Key := [(key2273, 2), (key2271, 2), (key2237, 2), (key2325, -2), (key2273, -2), (key2271, -2), (key2004, 2), (key2002, 2), (key1992, 2), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, -1), (key2002, -1), (key2004, -2), (key1995, -2), (key1992, -2), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, -1), (key1992, -1), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17842 : Integer.Sparse Key := [(key2271, 2), (key2271, 2), (key2325, 2), (key2237, -2), (key2273, -2), (key2273, -2), (key2271, 2), (key2271, 2), (key2325, 2), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2295, -1), (key2237, -2), (key2273, -2), (key2273, -2), (key1992, -1), (key2004, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2295, -1), (key1995, 4), (key1995, 4), (key2260, 4)]

def rawRow17843 : Integer.Sparse Key := [(key2271, 2), (key2325, 2), (key2271, 2), (key2273, -2), (key2237, -2), (key2273, -2), (key2271, 2), (key2325, 2), (key2271, 2), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key2273, -2), (key2237, -2), (key2273, -2), (key2004, -1), (key1992, -1), (key2295, -1), (key1992, -1), (key2295, -1), (key2004, -1), (key1995, 4), (key2260, 4), (key1995, 4)]

def rawRow17844 : Integer.Sparse Key := [(key2325, 2), (key2271, 2), (key2271, 2), (key2273, -2), (key2273, -2), (key2237, -2), (key2325, 2), (key2271, 2), (key2271, 2), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, -1), (key1992, -1), (key2273, -2), (key2273, -2), (key2237, -2), (key2295, -1), (key2295, -1), (key2004, -1), (key2004, -1), (key1992, -1), (key1992, -1), (key2260, 4), (key1995, 4), (key1995, 4)]

def rawRow17845 : Integer.Sparse Key := [(key2031, 2), (key2036, 2), (key2036, 2), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2031, 2), (key2036, 2), (key2036, 2), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2243, 2), (key2248, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2255, 2)]

def rawRow17846 : Integer.Sparse Key := [(key2036, 2), (key2031, 2), (key2036, 2), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2036, 2), (key2031, 2), (key2036, 2), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2248, 2), (key2243, 2), (key2255, 2), (key2243, 2), (key2255, 2), (key2248, 2)]

def rawRow17847 : Integer.Sparse Key := [(key2036, 2), (key2036, 2), (key2031, 2), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2036, 2), (key2036, 2), (key2031, 2), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2255, 2), (key2255, 2), (key2248, 2), (key2248, 2), (key2243, 2), (key2243, 2)]

def rawRow17848 : Integer.Sparse Key := [(key2061, 2), (key2066, 2), (key2093, 2), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2150, 2), (key2155, 2), (key2195, 2), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2)]

def rawRow17849 : Integer.Sparse Key := [(key2066, 2), (key2061, 2), (key2093, 2), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2155, 2), (key2150, 2), (key2195, 2), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2)]

def rawRow17850 : Integer.Sparse Key := [(key2061, 2), (key2093, 2), (key2066, 2), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, 2), (key2195, 2), (key2155, 2), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2)]

def rawRow17851 : Integer.Sparse Key := [(key2093, 2), (key2061, 2), (key2066, 2), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, 2), (key2150, 2), (key2155, 2), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2)]

def rawRow17852 : Integer.Sparse Key := [(key2066, 2), (key2093, 2), (key2061, 2), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2155, 2), (key2195, 2), (key2150, 2), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2)]

def rawRow17853 : Integer.Sparse Key := [(key2093, 2), (key2066, 2), (key2061, 2), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2195, 2), (key2155, 2), (key2150, 2), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2)]

def rawRow17854 : Integer.Sparse Key := [(key2150, 2), (key2155, 2), (key2195, 2), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, 2), (key2066, 2), (key2093, 2), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2)]

def rawRow17855 : Integer.Sparse Key := [(key2155, 2), (key2150, 2), (key2195, 2), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, 2), (key2061, 2), (key2093, 2), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2)]

def rawRow17856 : Integer.Sparse Key := [(key2150, 2), (key2195, 2), (key2155, 2), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2061, 2), (key2093, 2), (key2066, 2), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2)]

def rawRow17857 : Integer.Sparse Key := [(key2195, 2), (key2150, 2), (key2155, 2), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2093, 2), (key2061, 2), (key2066, 2), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2)]

def rawRow17858 : Integer.Sparse Key := [(key2155, 2), (key2195, 2), (key2150, 2), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2066, 2), (key2093, 2), (key2061, 2), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2)]

def rawRow17859 : Integer.Sparse Key := [(key2195, 2), (key2155, 2), (key2150, 2), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2093, 2), (key2066, 2), (key2061, 2), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2)]

def rawRow17860 : Integer.Sparse Key := [(key2243, 2), (key2304, 2), (key2304, 2), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2243, 2), (key2304, 2), (key2304, 2), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2031, 2), (key2096, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2201, 2)]

def rawRow17861 : Integer.Sparse Key := [(key2304, 2), (key2243, 2), (key2304, 2), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2304, 2), (key2243, 2), (key2304, 2), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2096, 2), (key2031, 2), (key2201, 2), (key2031, 2), (key2201, 2), (key2096, 2)]

def rawRow17862 : Integer.Sparse Key := [(key2304, 2), (key2304, 2), (key2243, 2), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2304, 2), (key2304, 2), (key2243, 2), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2201, 2), (key2201, 2), (key2096, 2), (key2096, 2), (key2031, 2), (key2031, 2)]

def rawRow17863 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2093, 2), (key2093, 2), (key2096, 2), (key2150, 1), (key2155, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, -2), (key2201, -2), (key2061, -1), (key2066, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2071, -1), (key2150, 1), (key2155, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2168, 1), (key2093, 2), (key2093, 2), (key2096, 2), (key2195, -2), (key2195, -2), (key2201, -2)]

def rawRow17864 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2093, 2), (key2096, 2), (key2093, 2), (key2155, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, -2), (key2195, -2), (key2066, -1), (key2061, -1), (key2071, -1), (key2061, -1), (key2071, -1), (key2066, -1), (key2155, 1), (key2150, 1), (key2168, 1), (key2150, 1), (key2168, 1), (key2155, 1), (key2093, 2), (key2096, 2), (key2093, 2), (key2195, -2), (key2201, -2), (key2195, -2)]

def rawRow17865 : Integer.Sparse Key := [(key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2096, 2), (key2093, 2), (key2093, 2), (key2168, 1), (key2168, 1), (key2155, 1), (key2155, 1), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, -2), (key2195, -2), (key2071, -1), (key2071, -1), (key2066, -1), (key2066, -1), (key2061, -1), (key2061, -1), (key2168, 1), (key2168, 1), (key2155, 1), (key2155, 1), (key2150, 1), (key2150, 1), (key2096, 2), (key2093, 2), (key2093, 2), (key2201, -2), (key2195, -2), (key2195, -2)]

def rawRow17866 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2036, 2), (key2066, 2), (key2071, 2), (key2031, 1), (key2036, 1), (key2150, 1), (key2168, 1), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, -2), (key2168, -2), (key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2061, 1), (key2066, 1), (key2243, 1), (key2255, 1), (key2304, 1), (key2311, 1), (key2195, 2), (key2304, 2), (key2306, 2), (key2093, -2), (key2304, -2), (key2311, -2)]

def rawRow17867 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, 2), (key2071, 2), (key2066, 2), (key2036, 1), (key2031, 1), (key2168, 1), (key2150, 1), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, -2), (key2155, -2), (key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2066, 1), (key2061, 1), (key2255, 1), (key2243, 1), (key2311, 1), (key2304, 1), (key2195, 2), (key2306, 2), (key2304, 2), (key2093, -2), (key2311, -2), (key2304, -2)]

def rawRow17868 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2066, 2), (key2036, 2), (key2071, 2), (key2150, 1), (key2195, 1), (key2031, 1), (key2201, 1), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, -2), (key2168, -2), (key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2243, 1), (key2304, 1), (key2061, 1), (key2311, 1), (key2066, 1), (key2255, 1), (key2304, 2), (key2195, 2), (key2306, 2), (key2304, -2), (key2093, -2), (key2311, -2)]

def rawRow17869 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2066, 2), (key2071, 2), (key2036, 2), (key2195, 1), (key2150, 1), (key2201, 1), (key2031, 1), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, -2), (key2036, -2), (key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, 1), (key2243, 1), (key2311, 1), (key2061, 1), (key2255, 1), (key2066, 1), (key2304, 2), (key2306, 2), (key2195, 2), (key2304, -2), (key2311, -2), (key2093, -2)]

def rawRow17870 : Integer.Sparse Key := [(key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2071, 2), (key2036, 2), (key2066, 2), (key2168, 1), (key2201, 1), (key2036, 1), (key2195, 1), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, -2), (key2155, -2), (key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2255, 1), (key2311, 1), (key2066, 1), (key2304, 1), (key2061, 1), (key2243, 1), (key2306, 2), (key2195, 2), (key2304, 2), (key2311, -2), (key2093, -2), (key2304, -2)]

def rawRow17871 : Integer.Sparse Key := [(key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2071, 2), (key2066, 2), (key2036, 2), (key2201, 1), (key2168, 1), (key2195, 1), (key2036, 1), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, -2), (key2036, -2), (key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2311, 1), (key2255, 1), (key2304, 1), (key2066, 1), (key2243, 1), (key2061, 1), (key2306, 2), (key2304, 2), (key2195, 2), (key2311, -2), (key2304, -2), (key2093, -2)]

def rawRow17872 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2243, -1), (key2248, -1), (key2304, -1), (key2306, -1), (key2195, 2), (key2304, 2), (key2306, 2), (key2061, 1), (key2066, 1), (key2243, 1), (key2255, 1), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, -2), (key2311, -2), (key2031, -1), (key2036, -1), (key2061, -1), (key2071, -1), (key2093, -1), (key2096, -1), (key2031, 1), (key2036, 1), (key2150, 1), (key2168, 1), (key2195, 1), (key2201, 1), (key2036, 2), (key2066, 2), (key2071, 2), (key2036, -2), (key2155, -2), (key2168, -2)]

def rawRow17873 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2248, -1), (key2243, -1), (key2306, -1), (key2304, -1), (key2195, 2), (key2306, 2), (key2304, 2), (key2066, 1), (key2061, 1), (key2255, 1), (key2243, 1), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, -2), (key2304, -2), (key2036, -1), (key2031, -1), (key2071, -1), (key2061, -1), (key2096, -1), (key2093, -1), (key2036, 1), (key2031, 1), (key2168, 1), (key2150, 1), (key2201, 1), (key2195, 1), (key2036, 2), (key2071, 2), (key2066, 2), (key2036, -2), (key2168, -2), (key2155, -2)]

def rawRow17874 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2150, -1), (key2306, -1), (key2155, -1), (key2248, -1), (key2304, 2), (key2195, 2), (key2306, 2), (key2243, 1), (key2304, 1), (key2061, 1), (key2311, 1), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, -2), (key2311, -2), (key2061, -1), (key2093, -1), (key2031, -1), (key2096, -1), (key2036, -1), (key2071, -1), (key2150, 1), (key2195, 1), (key2031, 1), (key2201, 1), (key2036, 1), (key2168, 1), (key2066, 2), (key2036, 2), (key2071, 2), (key2155, -2), (key2036, -2), (key2168, -2)]

def rawRow17875 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2306, -1), (key2150, -1), (key2248, -1), (key2155, -1), (key2304, 2), (key2306, 2), (key2195, 2), (key2304, 1), (key2243, 1), (key2311, 1), (key2061, 1), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, -2), (key2093, -2), (key2093, -1), (key2061, -1), (key2096, -1), (key2031, -1), (key2071, -1), (key2036, -1), (key2195, 1), (key2150, 1), (key2201, 1), (key2031, 1), (key2168, 1), (key2036, 1), (key2066, 2), (key2071, 2), (key2036, 2), (key2155, -2), (key2168, -2), (key2036, -2)]

def rawRow17876 : Integer.Sparse Key := [(key2248, -1), (key2306, -1), (key2155, -1), (key2304, -1), (key2150, -1), (key2243, -1), (key2306, 2), (key2195, 2), (key2304, 2), (key2255, 1), (key2311, 1), (key2066, 1), (key2304, 1), (key2061, 1), (key2243, 1), (key2311, -2), (key2093, -2), (key2304, -2), (key2071, -1), (key2096, -1), (key2036, -1), (key2093, -1), (key2031, -1), (key2061, -1), (key2168, 1), (key2201, 1), (key2036, 1), (key2195, 1), (key2031, 1), (key2150, 1), (key2071, 2), (key2036, 2), (key2066, 2), (key2168, -2), (key2036, -2), (key2155, -2)]

def rawRow17877 : Integer.Sparse Key := [(key2306, -1), (key2248, -1), (key2304, -1), (key2155, -1), (key2243, -1), (key2150, -1), (key2306, 2), (key2304, 2), (key2195, 2), (key2311, 1), (key2255, 1), (key2304, 1), (key2066, 1), (key2243, 1), (key2061, 1), (key2311, -2), (key2304, -2), (key2093, -2), (key2096, -1), (key2071, -1), (key2093, -1), (key2036, -1), (key2061, -1), (key2031, -1), (key2201, 1), (key2168, 1), (key2195, 1), (key2036, 1), (key2150, 1), (key2031, 1), (key2071, 2), (key2066, 2), (key2036, 2), (key2168, -2), (key2155, -2), (key2036, -2)]

def rawRow17878 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2155, 2), (key2155, 2), (key2248, 2), (key2061, 1), (key2093, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2311, 1), (key2066, -2), (key2066, -2), (key2255, -2), (key2150, -1), (key2195, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2306, -1), (key2061, 1), (key2093, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2311, 1), (key2155, 2), (key2155, 2), (key2248, 2), (key2066, -2), (key2066, -2), (key2255, -2)]

def rawRow17879 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2155, 2), (key2248, 2), (key2155, 2), (key2093, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2066, -2), (key2255, -2), (key2066, -2), (key2195, -1), (key2150, -1), (key2306, -1), (key2150, -1), (key2306, -1), (key2195, -1), (key2093, 1), (key2061, 1), (key2311, 1), (key2061, 1), (key2311, 1), (key2093, 1), (key2155, 2), (key2248, 2), (key2155, 2), (key2066, -2), (key2255, -2), (key2066, -2)]

def rawRow17880 : Integer.Sparse Key := [(key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2248, 2), (key2155, 2), (key2155, 2), (key2311, 1), (key2311, 1), (key2093, 1), (key2093, 1), (key2061, 1), (key2061, 1), (key2255, -2), (key2066, -2), (key2066, -2), (key2306, -1), (key2306, -1), (key2195, -1), (key2195, -1), (key2150, -1), (key2150, -1), (key2311, 1), (key2311, 1), (key2093, 1), (key2093, 1), (key2061, 1), (key2061, 1), (key2248, 2), (key2155, 2), (key2155, 2), (key2255, -2), (key2066, -2), (key2066, -2)]

def rawRow17881 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2070, -1), (key2080, 2), (key2080, 2), (key2086, 2), (key2150, 1), (key2153, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2167, 1), (key2177, -2), (key2177, -2), (key2188, -2), (key2061, -1), (key2064, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2070, -1), (key2150, 1), (key2153, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2167, 1), (key2080, 2), (key2080, 2), (key2086, 2), (key2177, -2), (key2177, -2), (key2188, -2)]

def rawRow17882 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2070, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2080, 2), (key2086, 2), (key2080, 2), (key2153, 1), (key2150, 1), (key2167, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2177, -2), (key2188, -2), (key2177, -2), (key2064, -1), (key2061, -1), (key2070, -1), (key2061, -1), (key2070, -1), (key2064, -1), (key2153, 1), (key2150, 1), (key2167, 1), (key2150, 1), (key2167, 1), (key2153, 1), (key2080, 2), (key2086, 2), (key2080, 2), (key2177, -2), (key2188, -2), (key2177, -2)]

def rawRow17883 : Integer.Sparse Key := [(key2070, -1), (key2070, -1), (key2064, -1), (key2064, -1), (key2061, -1), (key2061, -1), (key2086, 2), (key2080, 2), (key2080, 2), (key2167, 1), (key2167, 1), (key2153, 1), (key2153, 1), (key2150, 1), (key2150, 1), (key2188, -2), (key2177, -2), (key2177, -2), (key2070, -1), (key2070, -1), (key2064, -1), (key2064, -1), (key2061, -1), (key2061, -1), (key2167, 1), (key2167, 1), (key2153, 1), (key2153, 1), (key2150, 1), (key2150, 1), (key2086, 2), (key2080, 2), (key2080, 2), (key2188, -2), (key2177, -2), (key2177, -2)]

def rawRow17884 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2061, -1), (key2070, -1), (key2080, -1), (key2086, -1), (key2034, 2), (key2064, 2), (key2070, 2), (key2031, 1), (key2034, 1), (key2150, 1), (key2167, 1), (key2177, 1), (key2188, 1), (key2034, -2), (key2153, -2), (key2167, -2), (key2150, -1), (key2153, -1), (key2243, -1), (key2247, -1), (key2277, -1), (key2280, -1), (key2061, 1), (key2064, 1), (key2243, 1), (key2254, 1), (key2277, 1), (key2288, 1), (key2177, 2), (key2277, 2), (key2280, 2), (key2080, -2), (key2277, -2), (key2288, -2)]

def rawRow17885 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2070, -1), (key2061, -1), (key2086, -1), (key2080, -1), (key2034, 2), (key2070, 2), (key2064, 2), (key2034, 1), (key2031, 1), (key2167, 1), (key2150, 1), (key2188, 1), (key2177, 1), (key2034, -2), (key2167, -2), (key2153, -2), (key2153, -1), (key2150, -1), (key2247, -1), (key2243, -1), (key2280, -1), (key2277, -1), (key2064, 1), (key2061, 1), (key2254, 1), (key2243, 1), (key2288, 1), (key2277, 1), (key2177, 2), (key2280, 2), (key2277, 2), (key2080, -2), (key2288, -2), (key2277, -2)]

def rawRow17886 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2031, -1), (key2086, -1), (key2034, -1), (key2070, -1), (key2064, 2), (key2034, 2), (key2070, 2), (key2150, 1), (key2177, 1), (key2031, 1), (key2188, 1), (key2034, 1), (key2167, 1), (key2153, -2), (key2034, -2), (key2167, -2), (key2243, -1), (key2277, -1), (key2150, -1), (key2280, -1), (key2153, -1), (key2247, -1), (key2243, 1), (key2277, 1), (key2061, 1), (key2288, 1), (key2064, 1), (key2254, 1), (key2277, 2), (key2177, 2), (key2280, 2), (key2277, -2), (key2080, -2), (key2288, -2)]

def rawRow17887 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2086, -1), (key2031, -1), (key2070, -1), (key2034, -1), (key2064, 2), (key2070, 2), (key2034, 2), (key2177, 1), (key2150, 1), (key2188, 1), (key2031, 1), (key2167, 1), (key2034, 1), (key2153, -2), (key2167, -2), (key2034, -2), (key2277, -1), (key2243, -1), (key2280, -1), (key2150, -1), (key2247, -1), (key2153, -1), (key2277, 1), (key2243, 1), (key2288, 1), (key2061, 1), (key2254, 1), (key2064, 1), (key2277, 2), (key2280, 2), (key2177, 2), (key2277, -2), (key2288, -2), (key2080, -2)]

def rawRow17888 : Integer.Sparse Key := [(key2070, -1), (key2086, -1), (key2034, -1), (key2080, -1), (key2031, -1), (key2061, -1), (key2070, 2), (key2034, 2), (key2064, 2), (key2167, 1), (key2188, 1), (key2034, 1), (key2177, 1), (key2031, 1), (key2150, 1), (key2167, -2), (key2034, -2), (key2153, -2), (key2247, -1), (key2280, -1), (key2153, -1), (key2277, -1), (key2150, -1), (key2243, -1), (key2254, 1), (key2288, 1), (key2064, 1), (key2277, 1), (key2061, 1), (key2243, 1), (key2280, 2), (key2177, 2), (key2277, 2), (key2288, -2), (key2080, -2), (key2277, -2)]

def rawRow17889 : Integer.Sparse Key := [(key2086, -1), (key2070, -1), (key2080, -1), (key2034, -1), (key2061, -1), (key2031, -1), (key2070, 2), (key2064, 2), (key2034, 2), (key2188, 1), (key2167, 1), (key2177, 1), (key2034, 1), (key2150, 1), (key2031, 1), (key2167, -2), (key2153, -2), (key2034, -2), (key2280, -1), (key2247, -1), (key2277, -1), (key2153, -1), (key2243, -1), (key2150, -1), (key2288, 1), (key2254, 1), (key2277, 1), (key2064, 1), (key2243, 1), (key2061, 1), (key2280, 2), (key2277, 2), (key2177, 2), (key2288, -2), (key2277, -2), (key2080, -2)]

def rawRow17890 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2243, -1), (key2247, -1), (key2277, -1), (key2280, -1), (key2177, 2), (key2277, 2), (key2280, 2), (key2061, 1), (key2064, 1), (key2243, 1), (key2254, 1), (key2277, 1), (key2288, 1), (key2080, -2), (key2277, -2), (key2288, -2), (key2031, -1), (key2034, -1), (key2061, -1), (key2070, -1), (key2080, -1), (key2086, -1), (key2031, 1), (key2034, 1), (key2150, 1), (key2167, 1), (key2177, 1), (key2188, 1), (key2034, 2), (key2064, 2), (key2070, 2), (key2034, -2), (key2153, -2), (key2167, -2)]

def rawRow17891 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2247, -1), (key2243, -1), (key2280, -1), (key2277, -1), (key2177, 2), (key2280, 2), (key2277, 2), (key2064, 1), (key2061, 1), (key2254, 1), (key2243, 1), (key2288, 1), (key2277, 1), (key2080, -2), (key2288, -2), (key2277, -2), (key2034, -1), (key2031, -1), (key2070, -1), (key2061, -1), (key2086, -1), (key2080, -1), (key2034, 1), (key2031, 1), (key2167, 1), (key2150, 1), (key2188, 1), (key2177, 1), (key2034, 2), (key2070, 2), (key2064, 2), (key2034, -2), (key2167, -2), (key2153, -2)]

def rawRow17892 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2150, -1), (key2280, -1), (key2153, -1), (key2247, -1), (key2277, 2), (key2177, 2), (key2280, 2), (key2243, 1), (key2277, 1), (key2061, 1), (key2288, 1), (key2064, 1), (key2254, 1), (key2277, -2), (key2080, -2), (key2288, -2), (key2061, -1), (key2080, -1), (key2031, -1), (key2086, -1), (key2034, -1), (key2070, -1), (key2150, 1), (key2177, 1), (key2031, 1), (key2188, 1), (key2034, 1), (key2167, 1), (key2064, 2), (key2034, 2), (key2070, 2), (key2153, -2), (key2034, -2), (key2167, -2)]

def rawRow17893 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2280, -1), (key2150, -1), (key2247, -1), (key2153, -1), (key2277, 2), (key2280, 2), (key2177, 2), (key2277, 1), (key2243, 1), (key2288, 1), (key2061, 1), (key2254, 1), (key2064, 1), (key2277, -2), (key2288, -2), (key2080, -2), (key2080, -1), (key2061, -1), (key2086, -1), (key2031, -1), (key2070, -1), (key2034, -1), (key2177, 1), (key2150, 1), (key2188, 1), (key2031, 1), (key2167, 1), (key2034, 1), (key2064, 2), (key2070, 2), (key2034, 2), (key2153, -2), (key2167, -2), (key2034, -2)]

def rawRow17894 : Integer.Sparse Key := [(key2247, -1), (key2280, -1), (key2153, -1), (key2277, -1), (key2150, -1), (key2243, -1), (key2280, 2), (key2177, 2), (key2277, 2), (key2254, 1), (key2288, 1), (key2064, 1), (key2277, 1), (key2061, 1), (key2243, 1), (key2288, -2), (key2080, -2), (key2277, -2), (key2070, -1), (key2086, -1), (key2034, -1), (key2080, -1), (key2031, -1), (key2061, -1), (key2167, 1), (key2188, 1), (key2034, 1), (key2177, 1), (key2031, 1), (key2150, 1), (key2070, 2), (key2034, 2), (key2064, 2), (key2167, -2), (key2034, -2), (key2153, -2)]

def rawRow17895 : Integer.Sparse Key := [(key2280, -1), (key2247, -1), (key2277, -1), (key2153, -1), (key2243, -1), (key2150, -1), (key2280, 2), (key2277, 2), (key2177, 2), (key2288, 1), (key2254, 1), (key2277, 1), (key2064, 1), (key2243, 1), (key2061, 1), (key2288, -2), (key2277, -2), (key2080, -2), (key2086, -1), (key2070, -1), (key2080, -1), (key2034, -1), (key2061, -1), (key2031, -1), (key2188, 1), (key2167, 1), (key2177, 1), (key2034, 1), (key2150, 1), (key2031, 1), (key2070, 2), (key2064, 2), (key2034, 2), (key2167, -2), (key2153, -2), (key2034, -2)]

def rawRow17896 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2280, -1), (key2153, 2), (key2153, 2), (key2247, 2), (key2061, 1), (key2080, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2288, 1), (key2064, -2), (key2064, -2), (key2254, -2), (key2150, -1), (key2177, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2280, -1), (key2061, 1), (key2080, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2288, 1), (key2153, 2), (key2153, 2), (key2247, 2), (key2064, -2), (key2064, -2), (key2254, -2)]

def rawRow17897 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2280, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2153, 2), (key2247, 2), (key2153, 2), (key2080, 1), (key2061, 1), (key2288, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2064, -2), (key2254, -2), (key2064, -2), (key2177, -1), (key2150, -1), (key2280, -1), (key2150, -1), (key2280, -1), (key2177, -1), (key2080, 1), (key2061, 1), (key2288, 1), (key2061, 1), (key2288, 1), (key2080, 1), (key2153, 2), (key2247, 2), (key2153, 2), (key2064, -2), (key2254, -2), (key2064, -2)]

def rawRow17898 : Integer.Sparse Key := [(key2280, -1), (key2280, -1), (key2177, -1), (key2177, -1), (key2150, -1), (key2150, -1), (key2247, 2), (key2153, 2), (key2153, 2), (key2288, 1), (key2288, 1), (key2080, 1), (key2080, 1), (key2061, 1), (key2061, 1), (key2254, -2), (key2064, -2), (key2064, -2), (key2280, -1), (key2280, -1), (key2177, -1), (key2177, -1), (key2150, -1), (key2150, -1), (key2288, 1), (key2288, 1), (key2080, 1), (key2080, 1), (key2061, 1), (key2061, 1), (key2247, 2), (key2153, 2), (key2153, 2), (key2254, -2), (key2064, -2), (key2064, -2)]

def rawRow17899 : Integer.Sparse Key := [(key2154, 2), (key2154, 2), (key2170, 2), (key2178, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2190, -1), (key2154, 2), (key2154, 2), (key2170, 2), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2290, -1), (key2178, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2190, -1), (key2278, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2290, -1), (key2329, 2), (key2331, 2), (key2329, 2), (key2334, 2), (key2331, 2), (key2334, 2)]

def rawRow17900 : Integer.Sparse Key := [(key2154, 2), (key2170, 2), (key2154, 2), (key2180, -1), (key2178, -1), (key2190, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2154, 2), (key2170, 2), (key2154, 2), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2180, -1), (key2178, -1), (key2190, -1), (key2178, -1), (key2190, -1), (key2180, -1), (key2282, -1), (key2278, -1), (key2290, -1), (key2278, -1), (key2290, -1), (key2282, -1), (key2331, 2), (key2329, 2), (key2334, 2), (key2329, 2), (key2334, 2), (key2331, 2)]

def rawRow17901 : Integer.Sparse Key := [(key2170, 2), (key2154, 2), (key2154, 2), (key2190, -1), (key2190, -1), (key2180, -1), (key2180, -1), (key2178, -1), (key2178, -1), (key2170, 2), (key2154, 2), (key2154, 2), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2278, -1), (key2190, -1), (key2190, -1), (key2180, -1), (key2180, -1), (key2178, -1), (key2178, -1), (key2290, -1), (key2290, -1), (key2282, -1), (key2282, -1), (key2278, -1), (key2278, -1), (key2334, 2), (key2334, 2), (key2331, 2), (key2331, 2), (key2329, 2), (key2329, 2)]

def rawRow17902 : Integer.Sparse Key := [(key2035, 2), (key2178, 2), (key2190, 2), (key2035, -1), (key2038, -1), (key2154, -1), (key2170, -1), (key2180, -1), (key2190, -1), (key2065, 2), (key2278, 2), (key2290, 2), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, -1), (key2290, -1), (key2081, -1), (key2083, -1), (key2278, -1), (key2290, -1), (key2329, -1), (key2334, -1), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, -1), (key2334, -1), (key2083, 2), (key2088, 2), (key2180, 2), (key2190, 2), (key2282, 2), (key2290, 2)]

def rawRow17903 : Integer.Sparse Key := [(key2035, 2), (key2190, 2), (key2178, 2), (key2038, -1), (key2035, -1), (key2170, -1), (key2154, -1), (key2190, -1), (key2180, -1), (key2065, 2), (key2290, 2), (key2278, 2), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, -1), (key2282, -1), (key2083, -1), (key2081, -1), (key2290, -1), (key2278, -1), (key2334, -1), (key2329, -1), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, -1), (key2331, -1), (key2088, 2), (key2083, 2), (key2190, 2), (key2180, 2), (key2290, 2), (key2282, 2)]

def rawRow17904 : Integer.Sparse Key := [(key2178, 2), (key2035, 2), (key2190, 2), (key2154, -1), (key2180, -1), (key2035, -1), (key2190, -1), (key2038, -1), (key2170, -1), (key2278, 2), (key2065, 2), (key2290, 2), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, -1), (key2170, -1), (key2278, -1), (key2329, -1), (key2081, -1), (key2334, -1), (key2083, -1), (key2290, -1), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, -1), (key2190, -1), (key2180, 2), (key2282, 2), (key2083, 2), (key2290, 2), (key2088, 2), (key2190, 2)]

def rawRow17905 : Integer.Sparse Key := [(key2178, 2), (key2190, 2), (key2035, 2), (key2180, -1), (key2154, -1), (key2190, -1), (key2035, -1), (key2170, -1), (key2038, -1), (key2278, 2), (key2290, 2), (key2065, 2), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, -1), (key2073, -1), (key2329, -1), (key2278, -1), (key2334, -1), (key2081, -1), (key2290, -1), (key2083, -1), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, -1), (key2088, -1), (key2282, 2), (key2180, 2), (key2290, 2), (key2083, 2), (key2190, 2), (key2088, 2)]

def rawRow17906 : Integer.Sparse Key := [(key2190, 2), (key2035, 2), (key2178, 2), (key2170, -1), (key2190, -1), (key2038, -1), (key2180, -1), (key2035, -1), (key2154, -1), (key2290, 2), (key2065, 2), (key2278, 2), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, -1), (key2154, -1), (key2290, -1), (key2334, -1), (key2083, -1), (key2329, -1), (key2081, -1), (key2278, -1), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, -1), (key2178, -1), (key2190, 2), (key2290, 2), (key2088, 2), (key2282, 2), (key2083, 2), (key2180, 2)]

def rawRow17907 : Integer.Sparse Key := [(key2190, 2), (key2178, 2), (key2035, 2), (key2190, -1), (key2170, -1), (key2180, -1), (key2038, -1), (key2154, -1), (key2035, -1), (key2290, 2), (key2278, 2), (key2065, 2), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, -1), (key2065, -1), (key2334, -1), (key2290, -1), (key2329, -1), (key2083, -1), (key2278, -1), (key2081, -1), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, -1), (key2081, -1), (key2290, 2), (key2190, 2), (key2282, 2), (key2088, 2), (key2180, 2), (key2083, 2)]

def rawRow17908 : Integer.Sparse Key := [(key2065, 2), (key2278, 2), (key2290, 2), (key2081, -1), (key2083, -1), (key2278, -1), (key2290, -1), (key2329, -1), (key2334, -1), (key2035, 2), (key2178, 2), (key2190, 2), (key2081, -1), (key2088, -1), (key2178, -1), (key2190, -1), (key2331, -1), (key2334, -1), (key2035, -1), (key2038, -1), (key2154, -1), (key2170, -1), (key2180, -1), (key2190, -1), (key2065, -1), (key2073, -1), (key2154, -1), (key2170, -1), (key2282, -1), (key2290, -1), (key2083, 2), (key2088, 2), (key2180, 2), (key2190, 2), (key2282, 2), (key2290, 2)]

def rawRow17909 : Integer.Sparse Key := [(key2065, 2), (key2290, 2), (key2278, 2), (key2083, -1), (key2081, -1), (key2290, -1), (key2278, -1), (key2334, -1), (key2329, -1), (key2035, 2), (key2190, 2), (key2178, 2), (key2088, -1), (key2081, -1), (key2190, -1), (key2178, -1), (key2334, -1), (key2331, -1), (key2038, -1), (key2035, -1), (key2170, -1), (key2154, -1), (key2190, -1), (key2180, -1), (key2073, -1), (key2065, -1), (key2170, -1), (key2154, -1), (key2290, -1), (key2282, -1), (key2088, 2), (key2083, 2), (key2190, 2), (key2180, 2), (key2290, 2), (key2282, 2)]

def rawRow17910 : Integer.Sparse Key := [(key2278, 2), (key2065, 2), (key2290, 2), (key2278, -1), (key2329, -1), (key2081, -1), (key2334, -1), (key2083, -1), (key2290, -1), (key2178, 2), (key2035, 2), (key2190, 2), (key2178, -1), (key2331, -1), (key2081, -1), (key2334, -1), (key2088, -1), (key2190, -1), (key2154, -1), (key2180, -1), (key2035, -1), (key2190, -1), (key2038, -1), (key2170, -1), (key2154, -1), (key2282, -1), (key2065, -1), (key2290, -1), (key2073, -1), (key2170, -1), (key2180, 2), (key2282, 2), (key2083, 2), (key2290, 2), (key2088, 2), (key2190, 2)]

def rawRow17911 : Integer.Sparse Key := [(key2278, 2), (key2290, 2), (key2065, 2), (key2329, -1), (key2278, -1), (key2334, -1), (key2081, -1), (key2290, -1), (key2083, -1), (key2178, 2), (key2190, 2), (key2035, 2), (key2331, -1), (key2178, -1), (key2334, -1), (key2081, -1), (key2190, -1), (key2088, -1), (key2180, -1), (key2154, -1), (key2190, -1), (key2035, -1), (key2170, -1), (key2038, -1), (key2282, -1), (key2154, -1), (key2290, -1), (key2065, -1), (key2170, -1), (key2073, -1), (key2282, 2), (key2180, 2), (key2290, 2), (key2083, 2), (key2190, 2), (key2088, 2)]

def rawRow17912 : Integer.Sparse Key := [(key2290, 2), (key2065, 2), (key2278, 2), (key2290, -1), (key2334, -1), (key2083, -1), (key2329, -1), (key2081, -1), (key2278, -1), (key2190, 2), (key2035, 2), (key2178, 2), (key2190, -1), (key2334, -1), (key2088, -1), (key2331, -1), (key2081, -1), (key2178, -1), (key2170, -1), (key2190, -1), (key2038, -1), (key2180, -1), (key2035, -1), (key2154, -1), (key2170, -1), (key2290, -1), (key2073, -1), (key2282, -1), (key2065, -1), (key2154, -1), (key2190, 2), (key2290, 2), (key2088, 2), (key2282, 2), (key2083, 2), (key2180, 2)]

def rawRow17913 : Integer.Sparse Key := [(key2290, 2), (key2278, 2), (key2065, 2), (key2334, -1), (key2290, -1), (key2329, -1), (key2083, -1), (key2278, -1), (key2081, -1), (key2190, 2), (key2178, 2), (key2035, 2), (key2334, -1), (key2190, -1), (key2331, -1), (key2088, -1), (key2178, -1), (key2081, -1), (key2190, -1), (key2170, -1), (key2180, -1), (key2038, -1), (key2154, -1), (key2035, -1), (key2290, -1), (key2170, -1), (key2282, -1), (key2073, -1), (key2154, -1), (key2065, -1), (key2290, 2), (key2190, 2), (key2282, 2), (key2088, 2), (key2180, 2), (key2083, 2)]

def rawRow17914 : Integer.Sparse Key := [(key2081, 2), (key2081, 2), (key2334, 2), (key2065, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2290, -1), (key2081, 2), (key2081, 2), (key2334, 2), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2190, -1), (key2065, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2290, -1), (key2035, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2190, -1), (key2038, 2), (key2073, 2), (key2038, 2), (key2170, 2), (key2073, 2), (key2170, 2)]

def rawRow17915 : Integer.Sparse Key := [(key2081, 2), (key2334, 2), (key2081, 2), (key2083, -1), (key2065, -1), (key2290, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2081, 2), (key2334, 2), (key2081, 2), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2083, -1), (key2065, -1), (key2290, -1), (key2065, -1), (key2290, -1), (key2083, -1), (key2088, -1), (key2035, -1), (key2190, -1), (key2035, -1), (key2190, -1), (key2088, -1), (key2073, 2), (key2038, 2), (key2170, 2), (key2038, 2), (key2170, 2), (key2073, 2)]

def rawRow17916 : Integer.Sparse Key := [(key2334, 2), (key2081, 2), (key2081, 2), (key2290, -1), (key2290, -1), (key2083, -1), (key2083, -1), (key2065, -1), (key2065, -1), (key2334, 2), (key2081, 2), (key2081, 2), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, -1), (key2035, -1), (key2290, -1), (key2290, -1), (key2083, -1), (key2083, -1), (key2065, -1), (key2065, -1), (key2190, -1), (key2190, -1), (key2088, -1), (key2088, -1), (key2035, -1), (key2035, -1), (key2170, 2), (key2170, 2), (key2073, 2), (key2073, 2), (key2038, 2), (key2038, 2)]

def rawRow17917 : Integer.Sparse Key := [(key777, 4), (key782, 4), (key782, 4), (key802, -2), (key807, -2), (key802, -2), (key821, -2), (key807, -2), (key821, -2), (key802, -2), (key807, -2), (key802, -2), (key821, -2), (key807, -2), (key821, -2), (key872, 4), (key905, 4), (key905, 4)]

def rawRow17918 : Integer.Sparse Key := [(key782, 4), (key777, 4), (key782, 4), (key807, -2), (key802, -2), (key821, -2), (key802, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key821, -2), (key802, -2), (key821, -2), (key807, -2), (key905, 4), (key872, 4), (key905, 4)]

def rawRow17919 : Integer.Sparse Key := [(key782, 4), (key782, 4), (key777, 4), (key821, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key802, -2), (key821, -2), (key821, -2), (key807, -2), (key807, -2), (key802, -2), (key802, -2), (key905, 4), (key905, 4), (key872, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17920 : Integer.Sparse Key := [(key802, 4), (key807, 4), (key812, 4), (key777, -2), (key782, -2), (key802, -2), (key821, -2), (key812, -2), (key824, -2), (key802, -2), (key807, -2), (key872, -2), (key905, -2), (key877, -2), (key907, -2), (key802, 4), (key821, 4), (key907, 4)]

def rawRow17921 : Integer.Sparse Key := [(key807, 4), (key802, 4), (key812, 4), (key782, -2), (key777, -2), (key821, -2), (key802, -2), (key824, -2), (key812, -2), (key807, -2), (key802, -2), (key905, -2), (key872, -2), (key907, -2), (key877, -2), (key821, 4), (key802, 4), (key907, 4)]

def rawRow17922 : Integer.Sparse Key := [(key802, 4), (key812, 4), (key807, 4), (key802, -2), (key812, -2), (key777, -2), (key824, -2), (key782, -2), (key821, -2), (key872, -2), (key877, -2), (key802, -2), (key907, -2), (key807, -2), (key905, -2), (key802, 4), (key907, 4), (key821, 4)]

def rawRow17923 : Integer.Sparse Key := [(key812, 4), (key802, 4), (key807, 4), (key812, -2), (key802, -2), (key824, -2), (key777, -2), (key821, -2), (key782, -2), (key877, -2), (key872, -2), (key907, -2), (key802, -2), (key905, -2), (key807, -2), (key907, 4), (key802, 4), (key821, 4)]

def rawRow17924 : Integer.Sparse Key := [(key807, 4), (key812, 4), (key802, 4), (key821, -2), (key824, -2), (key782, -2), (key812, -2), (key777, -2), (key802, -2), (key905, -2), (key907, -2), (key807, -2), (key877, -2), (key802, -2), (key872, -2), (key821, 4), (key907, 4), (key802, 4)]

def rawRow17925 : Integer.Sparse Key := [(key812, 4), (key807, 4), (key802, 4), (key824, -2), (key821, -2), (key812, -2), (key782, -2), (key802, -2), (key777, -2), (key907, -2), (key905, -2), (key877, -2), (key807, -2), (key872, -2), (key802, -2), (key907, 4), (key821, 4), (key802, 4)]

def rawRow17926 : Integer.Sparse Key := [(key802, 4), (key807, 4), (key812, 4), (key802, -2), (key807, -2), (key872, -2), (key905, -2), (key877, -2), (key907, -2), (key777, -2), (key782, -2), (key802, -2), (key821, -2), (key812, -2), (key824, -2), (key802, 4), (key821, 4), (key907, 4)]

def rawRow17927 : Integer.Sparse Key := [(key807, 4), (key802, 4), (key812, 4), (key807, -2), (key802, -2), (key905, -2), (key872, -2), (key907, -2), (key877, -2), (key782, -2), (key777, -2), (key821, -2), (key802, -2), (key824, -2), (key812, -2), (key821, 4), (key802, 4), (key907, 4)]

def rawRow17928 : Integer.Sparse Key := [(key802, 4), (key812, 4), (key807, 4), (key872, -2), (key877, -2), (key802, -2), (key907, -2), (key807, -2), (key905, -2), (key802, -2), (key812, -2), (key777, -2), (key824, -2), (key782, -2), (key821, -2), (key802, 4), (key907, 4), (key821, 4)]

def rawRow17929 : Integer.Sparse Key := [(key812, 4), (key802, 4), (key807, 4), (key877, -2), (key872, -2), (key907, -2), (key802, -2), (key905, -2), (key807, -2), (key812, -2), (key802, -2), (key824, -2), (key777, -2), (key821, -2), (key782, -2), (key907, 4), (key802, 4), (key821, 4)]

def rawRow17930 : Integer.Sparse Key := [(key807, 4), (key812, 4), (key802, 4), (key905, -2), (key907, -2), (key807, -2), (key877, -2), (key802, -2), (key872, -2), (key821, -2), (key824, -2), (key782, -2), (key812, -2), (key777, -2), (key802, -2), (key821, 4), (key907, 4), (key802, 4)]

def rawRow17931 : Integer.Sparse Key := [(key812, 4), (key807, 4), (key802, 4), (key907, -2), (key905, -2), (key877, -2), (key807, -2), (key872, -2), (key802, -2), (key824, -2), (key821, -2), (key812, -2), (key782, -2), (key802, -2), (key777, -2), (key907, 4), (key821, 4), (key802, 4)]

def rawRow17932 : Integer.Sparse Key := [(key872, 4), (key877, 4), (key877, 4), (key802, -2), (key812, -2), (key802, -2), (key907, -2), (key812, -2), (key907, -2), (key802, -2), (key812, -2), (key802, -2), (key907, -2), (key812, -2), (key907, -2), (key777, 4), (key824, 4), (key824, 4)]

def rawRow17933 : Integer.Sparse Key := [(key877, 4), (key872, 4), (key877, 4), (key812, -2), (key802, -2), (key907, -2), (key802, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key907, -2), (key802, -2), (key907, -2), (key812, -2), (key824, 4), (key777, 4), (key824, 4)]

def rawRow17934 : Integer.Sparse Key := [(key877, 4), (key877, 4), (key872, 4), (key907, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key802, -2), (key907, -2), (key907, -2), (key812, -2), (key812, -2), (key802, -2), (key802, -2), (key824, 4), (key824, 4), (key777, 4)]

def rawRow17935 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key763, -2), (key785, -2), (key775, -2), (key785, -2), (key800, 2), (key810, 2), (key810, 2), (key835, 2), (key838, 2), (key838, 2), (key800, 2), (key810, 2), (key810, 2), (key933, -6), (key835, 2), (key838, 2), (key838, 2), (key933, -6)]

def rawRow17936 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key767, -2), (key773, -2), (key785, -2), (key775, -2), (key810, 2), (key800, 2), (key810, 2), (key838, 2), (key835, 2), (key838, 2), (key810, 2), (key800, 2), (key810, 2), (key933, -6), (key838, 2), (key835, 2), (key838, 2), (key933, -6)]

def rawRow17937 : Integer.Sparse Key := [(key767, -2), (key767, -2), (key765, -2), (key765, -2), (key773, -2), (key773, -2), (key810, 2), (key810, 2), (key800, 2), (key838, 2), (key838, 2), (key835, 2), (key810, 2), (key810, 2), (key800, 2), (key933, -6), (key838, 2), (key838, 2), (key835, 2), (key933, -6)]

def rawRow17938 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key788, -2), (key791, -2), (key790, -2), (key792, -2), (key763, 2), (key785, 2), (key838, 2), (key775, 2), (key785, 2), (key810, 2), (key800, 2), (key810, 2), (key933, 2), (key810, -6), (key835, 2), (key838, 2), (key933, 2), (key838, -6)]

def rawRow17939 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key791, -2), (key788, -2), (key792, -2), (key790, -2), (key767, 2), (key773, 2), (key838, 2), (key785, 2), (key775, 2), (key810, 2), (key810, 2), (key800, 2), (key933, 2), (key810, -6), (key838, 2), (key835, 2), (key933, 2), (key838, -6)]

def rawRow17940 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key763, -2), (key792, -2), (key765, -2), (key791, -2), (key763, 2), (key792, 2), (key785, 2), (key775, 2), (key810, 2), (key785, 2), (key800, 2), (key933, 2), (key810, 2), (key810, -6), (key835, 2), (key933, 2), (key838, 2), (key838, -6)]

def rawRow17941 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key792, -2), (key763, -2), (key791, -2), (key765, -2), (key792, 2), (key763, 2), (key785, 2), (key810, 2), (key775, 2), (key785, 2), (key933, 2), (key800, 2), (key810, 2), (key810, -6), (key933, 2), (key835, 2), (key838, 2), (key838, -6)]

def rawRow17942 : Integer.Sparse Key := [(key791, -2), (key792, -2), (key765, -2), (key790, -2), (key763, -2), (key788, -2), (key767, 2), (key792, 2), (key773, 2), (key785, 2), (key810, 2), (key775, 2), (key810, 2), (key933, 2), (key800, 2), (key810, -6), (key838, 2), (key933, 2), (key835, 2), (key838, -6)]

def rawRow17943 : Integer.Sparse Key := [(key792, -2), (key791, -2), (key790, -2), (key765, -2), (key788, -2), (key763, -2), (key792, 2), (key767, 2), (key773, 2), (key810, 2), (key785, 2), (key775, 2), (key933, 2), (key810, 2), (key800, 2), (key810, -6), (key933, 2), (key838, 2), (key835, 2), (key838, -6)]

def rawRow17944 : Integer.Sparse Key := [(key763, -2), (key765, -2), (key788, -2), (key791, -2), (key790, -2), (key792, -2), (key788, 2), (key791, 2), (key851, 2), (key790, 2), (key792, 2), (key851, 2), (key763, 2), (key785, 2), (key838, 2), (key838, -6), (key775, 2), (key785, 2), (key810, 2), (key810, -6)]

def rawRow17945 : Integer.Sparse Key := [(key765, -2), (key763, -2), (key791, -2), (key788, -2), (key792, -2), (key790, -2), (key791, 2), (key788, 2), (key851, 2), (key792, 2), (key790, 2), (key851, 2), (key767, 2), (key773, 2), (key838, 2), (key838, -6), (key785, 2), (key775, 2), (key810, 2), (key810, -6)]

def rawRow17946 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key763, -2), (key792, -2), (key765, -2), (key791, -2), (key788, 2), (key851, 2), (key791, 2), (key790, 2), (key851, 2), (key792, 2), (key763, 2), (key792, 2), (key785, 2), (key838, -6), (key775, 2), (key810, 2), (key785, 2), (key810, -6)]

def rawRow17947 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key792, -2), (key763, -2), (key791, -2), (key765, -2), (key851, 2), (key788, 2), (key791, 2), (key851, 2), (key790, 2), (key792, 2), (key792, 2), (key763, 2), (key785, 2), (key838, -6), (key810, 2), (key775, 2), (key785, 2), (key810, -6)]

def rawRow17948 : Integer.Sparse Key := [(key791, -2), (key792, -2), (key765, -2), (key790, -2), (key763, -2), (key788, -2), (key791, 2), (key851, 2), (key788, 2), (key792, 2), (key851, 2), (key790, 2), (key767, 2), (key792, 2), (key773, 2), (key838, -6), (key785, 2), (key810, 2), (key775, 2), (key810, -6)]

def rawRow17949 : Integer.Sparse Key := [(key792, -2), (key791, -2), (key790, -2), (key765, -2), (key788, -2), (key763, -2), (key851, 2), (key791, 2), (key788, 2), (key851, 2), (key792, 2), (key790, 2), (key792, 2), (key767, 2), (key773, 2), (key838, -6), (key810, 2), (key785, 2), (key775, 2), (key810, -6)]

def rawRow17950 : Integer.Sparse Key := [(key788, -2), (key790, -2), (key788, -2), (key851, -2), (key790, -2), (key851, -2), (key763, 2), (key792, 2), (key792, 2), (key765, 2), (key791, 2), (key791, 2), (key763, 2), (key792, 2), (key792, 2), (key785, -6), (key775, 2), (key810, 2), (key810, 2), (key785, -6)]

def rawRow17951 : Integer.Sparse Key := [(key790, -2), (key788, -2), (key851, -2), (key788, -2), (key851, -2), (key790, -2), (key792, 2), (key763, 2), (key792, 2), (key791, 2), (key765, 2), (key791, 2), (key792, 2), (key763, 2), (key792, 2), (key785, -6), (key810, 2), (key775, 2), (key810, 2), (key785, -6)]

def rawRow17952 : Integer.Sparse Key := [(key851, -2), (key851, -2), (key790, -2), (key790, -2), (key788, -2), (key788, -2), (key792, 2), (key792, 2), (key763, 2), (key791, 2), (key791, 2), (key765, 2), (key792, 2), (key792, 2), (key763, 2), (key785, -6), (key810, 2), (key810, 2), (key775, 2), (key785, -6)]

def rawRow17954 : Integer.Sparse Key := [(key636, 4), (key637, 4), (key636, 4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key651, 12)]

def rawRow17955 : Integer.Sparse Key := [(key637, 4), (key636, 4), (key636, 4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key651, 12)]

def rawRow17956 : Integer.Sparse Key := [(key636, 4), (key642, 4), (key643, 4), (key636, -4), (key637, -4), (key643, -4), (key642, -4), (key643, -4), (key651, -4), (key643, 12)]

def rawRow17957 : Integer.Sparse Key := [(key636, 4), (key643, 4), (key642, 4), (key637, -4), (key636, -4), (key643, -4), (key643, -4), (key642, -4), (key651, -4), (key643, 12)]

def rawRow17958 : Integer.Sparse Key := [(key642, 4), (key636, 4), (key643, 4), (key636, -4), (key643, -4), (key637, -4), (key642, -4), (key651, -4), (key643, -4), (key643, 12)]

def rawRow17959 : Integer.Sparse Key := [(key642, 4), (key643, 4), (key636, 4), (key643, -4), (key636, -4), (key637, -4), (key651, -4), (key642, -4), (key643, -4), (key643, 12)]

def rawRow17960 : Integer.Sparse Key := [(key643, 4), (key636, 4), (key642, 4), (key637, -4), (key643, -4), (key636, -4), (key643, -4), (key651, -4), (key642, -4), (key643, 12)]

def rawRow17961 : Integer.Sparse Key := [(key643, 4), (key642, 4), (key636, 4), (key643, -4), (key637, -4), (key636, -4), (key651, -4), (key643, -4), (key642, -4), (key643, 12)]

def rawRow17962 : Integer.Sparse Key := [(key636, 4), (key642, 4), (key643, 4), (key642, -4), (key643, -4), (key651, -4), (key636, -4), (key637, -4), (key643, -4), (key643, 12)]

def rawRow17963 : Integer.Sparse Key := [(key636, 4), (key643, 4), (key642, 4), (key643, -4), (key642, -4), (key651, -4), (key637, -4), (key636, -4), (key643, -4), (key643, 12)]

def rawRow17964 : Integer.Sparse Key := [(key642, 4), (key636, 4), (key643, 4), (key642, -4), (key651, -4), (key643, -4), (key636, -4), (key643, -4), (key637, -4), (key643, 12)]

def rawRow17965 : Integer.Sparse Key := [(key642, 4), (key643, 4), (key636, 4), (key651, -4), (key642, -4), (key643, -4), (key643, -4), (key636, -4), (key637, -4), (key643, 12)]

def rawRow17966 : Integer.Sparse Key := [(key643, 4), (key636, 4), (key642, 4), (key643, -4), (key651, -4), (key642, -4), (key637, -4), (key643, -4), (key636, -4), (key643, 12)]

def rawRow17967 : Integer.Sparse Key := [(key643, 4), (key642, 4), (key636, 4), (key651, -4), (key643, -4), (key642, -4), (key643, -4), (key637, -4), (key636, -4), (key643, 12)]

def rawRow17968 : Integer.Sparse Key := [(key642, 4), (key642, 4), (key651, 4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key637, 12)]

def rawRow17969 : Integer.Sparse Key := [(key642, 4), (key651, 4), (key642, 4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key637, 12)]

def rawRow17970 : Integer.Sparse Key := [(key651, 4), (key642, 4), (key642, 4), (key643, -4), (key643, -4), (key636, -4), (key643, -4), (key643, -4), (key636, -4), (key637, 12)]

def rawRow17971 : Integer.Sparse Key := [(key781, 4), (key784, 4), (key784, 4), (key806, -2), (key809, -2), (key806, -2), (key814, -2), (key809, -2), (key814, -2), (key806, -2), (key809, -2), (key806, -2), (key814, -2), (key809, -2), (key814, -2), (key875, 4), (key879, 4), (key879, 4)]

def rawRow17972 : Integer.Sparse Key := [(key784, 4), (key781, 4), (key784, 4), (key809, -2), (key806, -2), (key814, -2), (key806, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key814, -2), (key806, -2), (key814, -2), (key809, -2), (key879, 4), (key875, 4), (key879, 4)]

def rawRow17973 : Integer.Sparse Key := [(key784, 4), (key784, 4), (key781, 4), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key806, -2), (key814, -2), (key814, -2), (key809, -2), (key809, -2), (key806, -2), (key806, -2), (key879, 4), (key879, 4), (key875, 4)]

def rawRow17974 : Integer.Sparse Key := [(key806, 4), (key809, 4), (key814, 4), (key781, -2), (key784, -2), (key806, -2), (key814, -2), (key822, -2), (key827, -2), (key806, -2), (key809, -2), (key875, -2), (key879, -2), (key906, -2), (key910, -2), (key806, 4), (key814, 4), (key910, 4)]

def rawRow17975 : Integer.Sparse Key := [(key809, 4), (key806, 4), (key814, 4), (key784, -2), (key781, -2), (key814, -2), (key806, -2), (key827, -2), (key822, -2), (key809, -2), (key806, -2), (key879, -2), (key875, -2), (key910, -2), (key906, -2), (key814, 4), (key806, 4), (key910, 4)]

def rawRow17976 : Integer.Sparse Key := [(key806, 4), (key814, 4), (key809, 4), (key806, -2), (key814, -2), (key781, -2), (key827, -2), (key784, -2), (key814, -2), (key875, -2), (key906, -2), (key806, -2), (key910, -2), (key809, -2), (key879, -2), (key806, 4), (key910, 4), (key814, 4)]

def rawRow17977 : Integer.Sparse Key := [(key814, 4), (key806, 4), (key809, 4), (key814, -2), (key806, -2), (key827, -2), (key781, -2), (key814, -2), (key784, -2), (key906, -2), (key875, -2), (key910, -2), (key806, -2), (key879, -2), (key809, -2), (key910, 4), (key806, 4), (key814, 4)]

def rawRow17978 : Integer.Sparse Key := [(key809, 4), (key814, 4), (key806, 4), (key822, -2), (key827, -2), (key784, -2), (key814, -2), (key781, -2), (key806, -2), (key879, -2), (key910, -2), (key809, -2), (key906, -2), (key806, -2), (key875, -2), (key814, 4), (key910, 4), (key806, 4)]

def rawRow17979 : Integer.Sparse Key := [(key814, 4), (key809, 4), (key806, 4), (key827, -2), (key822, -2), (key814, -2), (key784, -2), (key806, -2), (key781, -2), (key910, -2), (key879, -2), (key906, -2), (key809, -2), (key875, -2), (key806, -2), (key910, 4), (key814, 4), (key806, 4)]

def rawRow17980 : Integer.Sparse Key := [(key806, 4), (key809, 4), (key814, 4), (key806, -2), (key809, -2), (key875, -2), (key906, -2), (key879, -2), (key910, -2), (key781, -2), (key784, -2), (key806, -2), (key814, -2), (key822, -2), (key827, -2), (key806, 4), (key814, 4), (key910, 4)]

def rawRow17981 : Integer.Sparse Key := [(key809, 4), (key806, 4), (key814, 4), (key809, -2), (key806, -2), (key906, -2), (key875, -2), (key910, -2), (key879, -2), (key784, -2), (key781, -2), (key814, -2), (key806, -2), (key827, -2), (key822, -2), (key814, 4), (key806, 4), (key910, 4)]

def rawRow17982 : Integer.Sparse Key := [(key806, 4), (key814, 4), (key809, 4), (key875, -2), (key879, -2), (key806, -2), (key910, -2), (key809, -2), (key906, -2), (key806, -2), (key814, -2), (key781, -2), (key827, -2), (key784, -2), (key814, -2), (key806, 4), (key910, 4), (key814, 4)]

def rawRow17983 : Integer.Sparse Key := [(key814, 4), (key806, 4), (key809, 4), (key879, -2), (key875, -2), (key910, -2), (key806, -2), (key906, -2), (key809, -2), (key814, -2), (key806, -2), (key827, -2), (key781, -2), (key814, -2), (key784, -2), (key910, 4), (key806, 4), (key814, 4)]

def rawRow17984 : Integer.Sparse Key := [(key809, 4), (key814, 4), (key806, 4), (key906, -2), (key910, -2), (key809, -2), (key879, -2), (key806, -2), (key875, -2), (key822, -2), (key827, -2), (key784, -2), (key814, -2), (key781, -2), (key806, -2), (key814, 4), (key910, 4), (key806, 4)]

def rawRow17985 : Integer.Sparse Key := [(key814, 4), (key809, 4), (key806, 4), (key910, -2), (key906, -2), (key879, -2), (key809, -2), (key875, -2), (key806, -2), (key827, -2), (key822, -2), (key814, -2), (key784, -2), (key806, -2), (key781, -2), (key910, 4), (key814, 4), (key806, 4)]

def rawRow17986 : Integer.Sparse Key := [(key875, 4), (key879, 4), (key879, 4), (key806, -2), (key814, -2), (key806, -2), (key910, -2), (key814, -2), (key910, -2), (key806, -2), (key814, -2), (key806, -2), (key910, -2), (key814, -2), (key910, -2), (key781, 4), (key827, 4), (key827, 4)]

def rawRow17987 : Integer.Sparse Key := [(key879, 4), (key875, 4), (key879, 4), (key814, -2), (key806, -2), (key910, -2), (key806, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key910, -2), (key806, -2), (key910, -2), (key814, -2), (key827, 4), (key781, 4), (key827, 4)]

def rawRow17988 : Integer.Sparse Key := [(key879, 4), (key879, 4), (key875, 4), (key910, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key806, -2), (key910, -2), (key910, -2), (key814, -2), (key814, -2), (key806, -2), (key806, -2), (key827, 4), (key827, 4), (key781, 4)]

def rawRow17989 : Integer.Sparse Key := [(key2421, 4), (key2496, 4), (key2550, 4), (key2428, -2), (key2429, -2), (key2496, -2), (key2550, -2), (key2508, -2), (key2556, -2), (key2428, -2), (key2429, -2), (key2496, -2), (key2550, -2), (key2508, -2), (key2556, -2), (key2442, 4), (key2508, 4), (key2556, 4)]

def rawRow17990 : Integer.Sparse Key := [(key2421, 4), (key2550, 4), (key2496, 4), (key2429, -2), (key2428, -2), (key2550, -2), (key2496, -2), (key2556, -2), (key2508, -2), (key2429, -2), (key2428, -2), (key2550, -2), (key2496, -2), (key2556, -2), (key2508, -2), (key2442, 4), (key2556, 4), (key2508, 4)]

def rawRow17991 : Integer.Sparse Key := [(key2496, 4), (key2421, 4), (key2550, 4), (key2496, -2), (key2508, -2), (key2428, -2), (key2556, -2), (key2429, -2), (key2550, -2), (key2496, -2), (key2508, -2), (key2428, -2), (key2556, -2), (key2429, -2), (key2550, -2), (key2508, 4), (key2442, 4), (key2556, 4)]

def rawRow17992 : Integer.Sparse Key := [(key2496, 4), (key2550, 4), (key2421, 4), (key2508, -2), (key2496, -2), (key2556, -2), (key2428, -2), (key2550, -2), (key2429, -2), (key2508, -2), (key2496, -2), (key2556, -2), (key2428, -2), (key2550, -2), (key2429, -2), (key2508, 4), (key2556, 4), (key2442, 4)]

def rawRow17993 : Integer.Sparse Key := [(key2550, 4), (key2421, 4), (key2496, 4), (key2550, -2), (key2556, -2), (key2429, -2), (key2508, -2), (key2428, -2), (key2496, -2), (key2550, -2), (key2556, -2), (key2429, -2), (key2508, -2), (key2428, -2), (key2496, -2), (key2556, 4), (key2442, 4), (key2508, 4)]

def rawRow17994 : Integer.Sparse Key := [(key2550, 4), (key2496, 4), (key2421, 4), (key2556, -2), (key2550, -2), (key2508, -2), (key2429, -2), (key2496, -2), (key2428, -2), (key2556, -2), (key2550, -2), (key2508, -2), (key2429, -2), (key2496, -2), (key2428, -2), (key2556, 4), (key2508, 4), (key2442, 4)]

def rawRow17995 : Integer.Sparse Key := [(key2428, 4), (key2428, 4), (key2556, 4), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2428, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2556, -2), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow17996 : Integer.Sparse Key := [(key2428, 4), (key2556, 4), (key2428, 4), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow17997 : Integer.Sparse Key := [(key2556, 4), (key2428, 4), (key2428, 4), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2556, -2), (key2556, -2), (key2442, -2), (key2442, -2), (key2428, -2), (key2428, -2), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow17998 : Integer.Sparse Key := [(key2429, 4), (key2429, 4), (key2508, 4), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2429, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2508, -2), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow17999 : Integer.Sparse Key := [(key2429, 4), (key2508, 4), (key2429, 4), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18000 : Integer.Sparse Key := [(key2508, 4), (key2429, 4), (key2429, 4), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2508, -2), (key2508, -2), (key2442, -2), (key2442, -2), (key2429, -2), (key2429, -2), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18001 : Integer.Sparse Key := [(key2428, 4), (key2428, 4), (key2556, 4), (key2428, -2), (key2442, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2556, -2), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow18002 : Integer.Sparse Key := [(key2428, 4), (key2556, 4), (key2428, 4), (key2442, -2), (key2428, -2), (key2556, -2), (key2428, -2), (key2556, -2), (key2442, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow18003 : Integer.Sparse Key := [(key2556, 4), (key2428, 4), (key2428, 4), (key2556, -2), (key2556, -2), (key2442, -2), (key2442, -2), (key2428, -2), (key2428, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow18004 : Integer.Sparse Key := [(key2442, 4), (key2442, 4), (key2442, 4), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18005 : Integer.Sparse Key := [(key2429, 4), (key2429, 4), (key2508, 4), (key2429, -2), (key2442, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2508, -2), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow18006 : Integer.Sparse Key := [(key2429, 4), (key2508, 4), (key2429, 4), (key2442, -2), (key2429, -2), (key2508, -2), (key2429, -2), (key2508, -2), (key2442, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18007 : Integer.Sparse Key := [(key2508, 4), (key2429, 4), (key2429, 4), (key2508, -2), (key2508, -2), (key2442, -2), (key2442, -2), (key2429, -2), (key2429, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18008 : Integer.Sparse Key := [(key2442, 4), (key2442, 4), (key2442, 4), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18009 : Integer.Sparse Key := [(key1049, -2), (key1052, -2), (key1060, -2), (key1060, 6), (key1049, -2), (key1052, -2), (key1060, -2), (key1049, 2), (key1052, 2), (key1135, 2), (key1205, 2), (key1140, 2), (key1207, 2), (key1060, -2), (key1140, -2), (key1207, -2), (key1060, 6), (key1060, -2), (key1140, -2), (key1207, -2)]

def rawRow18010 : Integer.Sparse Key := [(key1052, -2), (key1049, -2), (key1060, -2), (key1060, 6), (key1052, -2), (key1049, -2), (key1060, -2), (key1052, 2), (key1049, 2), (key1205, 2), (key1135, 2), (key1207, 2), (key1140, 2), (key1060, -2), (key1207, -2), (key1140, -2), (key1060, 6), (key1060, -2), (key1207, -2), (key1140, -2)]

def rawRow18011 : Integer.Sparse Key := [(key1049, -2), (key1060, -2), (key1052, -2), (key1060, 6), (key1049, -2), (key1060, -2), (key1052, -2), (key1135, 2), (key1140, 2), (key1049, 2), (key1207, 2), (key1052, 2), (key1205, 2), (key1140, -2), (key1060, -2), (key1207, -2), (key1060, 6), (key1140, -2), (key1060, -2), (key1207, -2)]

def rawRow18012 : Integer.Sparse Key := [(key1060, -2), (key1049, -2), (key1052, -2), (key1060, 6), (key1060, -2), (key1049, -2), (key1052, -2), (key1140, 2), (key1135, 2), (key1207, 2), (key1049, 2), (key1205, 2), (key1052, 2), (key1140, -2), (key1207, -2), (key1060, -2), (key1060, 6), (key1140, -2), (key1207, -2), (key1060, -2)]

def rawRow18013 : Integer.Sparse Key := [(key1052, -2), (key1060, -2), (key1049, -2), (key1060, 6), (key1052, -2), (key1060, -2), (key1049, -2), (key1205, 2), (key1207, 2), (key1052, 2), (key1140, 2), (key1049, 2), (key1135, 2), (key1207, -2), (key1060, -2), (key1140, -2), (key1060, 6), (key1207, -2), (key1060, -2), (key1140, -2)]

def rawRow18014 : Integer.Sparse Key := [(key1060, -2), (key1052, -2), (key1049, -2), (key1060, 6), (key1060, -2), (key1052, -2), (key1049, -2), (key1207, 2), (key1205, 2), (key1140, 2), (key1052, 2), (key1135, 2), (key1049, 2), (key1207, -2), (key1140, -2), (key1060, -2), (key1060, 6), (key1207, -2), (key1140, -2), (key1060, -2)]

def rawRow18015 : Integer.Sparse Key := [(key1049, -2), (key1060, -2), (key1060, -2), (key1052, 6), (key1135, -2), (key1140, -2), (key1140, -2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1052, -2), (key1052, -2), (key1205, -2), (key1140, 6), (key1060, -2), (key1060, -2), (key1207, -2)]

def rawRow18016 : Integer.Sparse Key := [(key1060, -2), (key1049, -2), (key1060, -2), (key1052, 6), (key1140, -2), (key1135, -2), (key1140, -2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1052, -2), (key1205, -2), (key1052, -2), (key1140, 6), (key1060, -2), (key1207, -2), (key1060, -2)]

def rawRow18017 : Integer.Sparse Key := [(key1060, -2), (key1060, -2), (key1049, -2), (key1052, 6), (key1140, -2), (key1140, -2), (key1135, -2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1205, -2), (key1052, -2), (key1052, -2), (key1140, 6), (key1207, -2), (key1060, -2), (key1060, -2)]

def rawRow18018 : Integer.Sparse Key := [(key1052, -2), (key1060, -2), (key1060, -2), (key1049, 6), (key1205, -2), (key1207, -2), (key1207, -2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1049, -2), (key1049, -2), (key1135, -2), (key1207, 6), (key1060, -2), (key1060, -2), (key1140, -2)]

def rawRow18019 : Integer.Sparse Key := [(key1060, -2), (key1052, -2), (key1060, -2), (key1049, 6), (key1207, -2), (key1205, -2), (key1207, -2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1049, -2), (key1135, -2), (key1049, -2), (key1207, 6), (key1060, -2), (key1140, -2), (key1060, -2)]

def rawRow18020 : Integer.Sparse Key := [(key1060, -2), (key1060, -2), (key1052, -2), (key1049, 6), (key1207, -2), (key1207, -2), (key1205, -2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1135, -2), (key1049, -2), (key1049, -2), (key1207, 6), (key1140, -2), (key1060, -2), (key1060, -2)]

def rawRow18021 : Integer.Sparse Key := [(key1135, -2), (key1140, -2), (key1140, -2), (key1140, 6), (key1049, -2), (key1060, -2), (key1060, -2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1060, -2), (key1060, -2), (key1207, -2), (key1052, 6), (key1052, -2), (key1052, -2), (key1205, -2)]

def rawRow18022 : Integer.Sparse Key := [(key1140, -2), (key1135, -2), (key1140, -2), (key1140, 6), (key1060, -2), (key1049, -2), (key1060, -2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, -2), (key1207, -2), (key1060, -2), (key1052, 6), (key1052, -2), (key1205, -2), (key1052, -2)]

def rawRow18023 : Integer.Sparse Key := [(key1140, -2), (key1140, -2), (key1135, -2), (key1140, 6), (key1060, -2), (key1060, -2), (key1049, -2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1207, -2), (key1060, -2), (key1060, -2), (key1052, 6), (key1205, -2), (key1052, -2), (key1052, -2)]

def rawRow18024 : Integer.Sparse Key := [(key1140, -2), (key1140, -2), (key1140, -2), (key1135, 6), (key1207, -2), (key1207, -2), (key1207, -2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1049, -2), (key1049, -2), (key1049, -2), (key1205, 6), (key1052, -2), (key1052, -2), (key1052, -2)]

def rawRow18025 : Integer.Sparse Key := [(key1205, -2), (key1207, -2), (key1207, -2), (key1207, 6), (key1052, -2), (key1060, -2), (key1060, -2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1060, -2), (key1060, -2), (key1140, -2), (key1049, 6), (key1049, -2), (key1049, -2), (key1135, -2)]

def rawRow18026 : Integer.Sparse Key := [(key1207, -2), (key1205, -2), (key1207, -2), (key1207, 6), (key1060, -2), (key1052, -2), (key1060, -2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, -2), (key1140, -2), (key1060, -2), (key1049, 6), (key1049, -2), (key1135, -2), (key1049, -2)]

def rawRow18027 : Integer.Sparse Key := [(key1207, -2), (key1207, -2), (key1205, -2), (key1207, 6), (key1060, -2), (key1060, -2), (key1052, -2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1140, -2), (key1060, -2), (key1060, -2), (key1049, 6), (key1135, -2), (key1049, -2), (key1049, -2)]

def rawRow18028 : Integer.Sparse Key := [(key1207, -2), (key1207, -2), (key1207, -2), (key1205, 6), (key1140, -2), (key1140, -2), (key1140, -2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1052, -2), (key1052, -2), (key1052, -2), (key1135, 6), (key1049, -2), (key1049, -2), (key1049, -2)]

def rawRow18029 : Integer.Sparse Key := [(key2415, -2), (key2418, -2), (key2425, -2), (key2425, 6), (key2415, -2), (key2418, -2), (key2425, -2), (key2415, 2), (key2418, 2), (key2488, 2), (key2547, 2), (key2493, 2), (key2549, 2), (key2425, -2), (key2493, -2), (key2549, -2), (key2425, 6), (key2425, -2), (key2493, -2), (key2549, -2)]

def rawRow18030 : Integer.Sparse Key := [(key2418, -2), (key2415, -2), (key2425, -2), (key2425, 6), (key2418, -2), (key2415, -2), (key2425, -2), (key2418, 2), (key2415, 2), (key2547, 2), (key2488, 2), (key2549, 2), (key2493, 2), (key2425, -2), (key2549, -2), (key2493, -2), (key2425, 6), (key2425, -2), (key2549, -2), (key2493, -2)]

def rawRow18031 : Integer.Sparse Key := [(key2415, -2), (key2425, -2), (key2418, -2), (key2425, 6), (key2415, -2), (key2425, -2), (key2418, -2), (key2488, 2), (key2493, 2), (key2415, 2), (key2549, 2), (key2418, 2), (key2547, 2), (key2493, -2), (key2425, -2), (key2549, -2), (key2425, 6), (key2493, -2), (key2425, -2), (key2549, -2)]

def rawRow18032 : Integer.Sparse Key := [(key2425, -2), (key2415, -2), (key2418, -2), (key2425, 6), (key2425, -2), (key2415, -2), (key2418, -2), (key2493, 2), (key2488, 2), (key2549, 2), (key2415, 2), (key2547, 2), (key2418, 2), (key2493, -2), (key2549, -2), (key2425, -2), (key2425, 6), (key2493, -2), (key2549, -2), (key2425, -2)]

def rawRow18033 : Integer.Sparse Key := [(key2418, -2), (key2425, -2), (key2415, -2), (key2425, 6), (key2418, -2), (key2425, -2), (key2415, -2), (key2547, 2), (key2549, 2), (key2418, 2), (key2493, 2), (key2415, 2), (key2488, 2), (key2549, -2), (key2425, -2), (key2493, -2), (key2425, 6), (key2549, -2), (key2425, -2), (key2493, -2)]

def rawRow18034 : Integer.Sparse Key := [(key2425, -2), (key2418, -2), (key2415, -2), (key2425, 6), (key2425, -2), (key2418, -2), (key2415, -2), (key2549, 2), (key2547, 2), (key2493, 2), (key2418, 2), (key2488, 2), (key2415, 2), (key2549, -2), (key2493, -2), (key2425, -2), (key2425, 6), (key2549, -2), (key2493, -2), (key2425, -2)]

def rawRow18035 : Integer.Sparse Key := [(key2415, -2), (key2425, -2), (key2425, -2), (key2418, 6), (key2488, -2), (key2493, -2), (key2493, -2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2418, -2), (key2418, -2), (key2547, -2), (key2493, 6), (key2425, -2), (key2425, -2), (key2549, -2)]

def rawRow18036 : Integer.Sparse Key := [(key2425, -2), (key2415, -2), (key2425, -2), (key2418, 6), (key2493, -2), (key2488, -2), (key2493, -2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2418, -2), (key2547, -2), (key2418, -2), (key2493, 6), (key2425, -2), (key2549, -2), (key2425, -2)]

def rawRow18037 : Integer.Sparse Key := [(key2425, -2), (key2425, -2), (key2415, -2), (key2418, 6), (key2493, -2), (key2493, -2), (key2488, -2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2547, -2), (key2418, -2), (key2418, -2), (key2493, 6), (key2549, -2), (key2425, -2), (key2425, -2)]

def rawRow18038 : Integer.Sparse Key := [(key2418, -2), (key2425, -2), (key2425, -2), (key2415, 6), (key2547, -2), (key2549, -2), (key2549, -2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2415, -2), (key2415, -2), (key2488, -2), (key2549, 6), (key2425, -2), (key2425, -2), (key2493, -2)]

def rawRow18039 : Integer.Sparse Key := [(key2425, -2), (key2418, -2), (key2425, -2), (key2415, 6), (key2549, -2), (key2547, -2), (key2549, -2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2415, -2), (key2488, -2), (key2415, -2), (key2549, 6), (key2425, -2), (key2493, -2), (key2425, -2)]

def rawRow18040 : Integer.Sparse Key := [(key2425, -2), (key2425, -2), (key2418, -2), (key2415, 6), (key2549, -2), (key2549, -2), (key2547, -2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2488, -2), (key2415, -2), (key2415, -2), (key2549, 6), (key2493, -2), (key2425, -2), (key2425, -2)]

def rawRow18041 : Integer.Sparse Key := [(key2488, -2), (key2493, -2), (key2493, -2), (key2493, 6), (key2415, -2), (key2425, -2), (key2425, -2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2425, -2), (key2425, -2), (key2549, -2), (key2418, 6), (key2418, -2), (key2418, -2), (key2547, -2)]

def rawRow18042 : Integer.Sparse Key := [(key2493, -2), (key2488, -2), (key2493, -2), (key2493, 6), (key2425, -2), (key2415, -2), (key2425, -2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, -2), (key2549, -2), (key2425, -2), (key2418, 6), (key2418, -2), (key2547, -2), (key2418, -2)]

def rawRow18043 : Integer.Sparse Key := [(key2493, -2), (key2493, -2), (key2488, -2), (key2493, 6), (key2425, -2), (key2425, -2), (key2415, -2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2549, -2), (key2425, -2), (key2425, -2), (key2418, 6), (key2547, -2), (key2418, -2), (key2418, -2)]

def rawRow18044 : Integer.Sparse Key := [(key2493, -2), (key2493, -2), (key2493, -2), (key2488, 6), (key2549, -2), (key2549, -2), (key2549, -2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2415, -2), (key2415, -2), (key2415, -2), (key2547, 6), (key2418, -2), (key2418, -2), (key2418, -2)]

def rawRow18045 : Integer.Sparse Key := [(key2547, -2), (key2549, -2), (key2549, -2), (key2549, 6), (key2418, -2), (key2425, -2), (key2425, -2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2425, -2), (key2425, -2), (key2493, -2), (key2415, 6), (key2415, -2), (key2415, -2), (key2488, -2)]

def rawRow18046 : Integer.Sparse Key := [(key2549, -2), (key2547, -2), (key2549, -2), (key2549, 6), (key2425, -2), (key2418, -2), (key2425, -2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, -2), (key2493, -2), (key2425, -2), (key2415, 6), (key2415, -2), (key2488, -2), (key2415, -2)]

def rawRow18047 : Integer.Sparse Key := [(key2549, -2), (key2549, -2), (key2547, -2), (key2549, 6), (key2425, -2), (key2425, -2), (key2418, -2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2493, -2), (key2425, -2), (key2425, -2), (key2415, 6), (key2488, -2), (key2415, -2), (key2415, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18048 : Integer.Sparse Key := [(key2549, -2), (key2549, -2), (key2549, -2), (key2547, 6), (key2493, -2), (key2493, -2), (key2493, -2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2418, -2), (key2418, -2), (key2418, -2), (key2488, 6), (key2415, -2), (key2415, -2), (key2415, -2)]

def rawRow18049 : Integer.Sparse Key := [(key3046, 6), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, 6), (key3046, -2), (key3095, -2), (key3101, -2), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3060, 2), (key3064, 2), (key3095, 2), (key3101, 2), (key3123, 2), (key3125, 2)]

def rawRow18050 : Integer.Sparse Key := [(key3046, 6), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, 6), (key3046, -2), (key3101, -2), (key3095, -2), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3064, 2), (key3060, 2), (key3101, 2), (key3095, 2), (key3125, 2), (key3123, 2)]

def rawRow18051 : Integer.Sparse Key := [(key3046, 6), (key3060, -2), (key3046, -2), (key3064, -2), (key3046, 6), (key3095, -2), (key3046, -2), (key3101, -2), (key3060, -2), (key3046, -2), (key3064, -2), (key3095, -2), (key3046, -2), (key3101, -2), (key3095, 2), (key3123, 2), (key3060, 2), (key3125, 2), (key3064, 2), (key3101, 2)]

def rawRow18052 : Integer.Sparse Key := [(key3046, 6), (key3060, -2), (key3064, -2), (key3046, -2), (key3046, 6), (key3095, -2), (key3101, -2), (key3046, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3046, -2), (key3123, 2), (key3095, 2), (key3125, 2), (key3060, 2), (key3101, 2), (key3064, 2)]

def rawRow18053 : Integer.Sparse Key := [(key3046, 6), (key3064, -2), (key3046, -2), (key3060, -2), (key3046, 6), (key3101, -2), (key3046, -2), (key3095, -2), (key3064, -2), (key3046, -2), (key3060, -2), (key3101, -2), (key3046, -2), (key3095, -2), (key3101, 2), (key3125, 2), (key3064, 2), (key3123, 2), (key3060, 2), (key3095, 2)]

def rawRow18054 : Integer.Sparse Key := [(key3046, 6), (key3064, -2), (key3060, -2), (key3046, -2), (key3046, 6), (key3101, -2), (key3095, -2), (key3046, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3046, -2), (key3125, 2), (key3101, 2), (key3123, 2), (key3064, 2), (key3095, 2), (key3060, 2)]

def rawRow18055 : Integer.Sparse Key := [(key3060, 6), (key3046, -2), (key3046, -2), (key3064, -2), (key3095, 6), (key3046, -2), (key3046, -2), (key3101, -2), (key3095, -2), (key3095, -2), (key3123, -2), (key3060, -2), (key3060, -2), (key3125, -2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

def rawRow18056 : Integer.Sparse Key := [(key3060, 6), (key3046, -2), (key3064, -2), (key3046, -2), (key3095, 6), (key3046, -2), (key3101, -2), (key3046, -2), (key3095, -2), (key3123, -2), (key3095, -2), (key3060, -2), (key3125, -2), (key3060, -2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

def rawRow18057 : Integer.Sparse Key := [(key3060, 6), (key3064, -2), (key3046, -2), (key3046, -2), (key3095, 6), (key3101, -2), (key3046, -2), (key3046, -2), (key3123, -2), (key3095, -2), (key3095, -2), (key3125, -2), (key3060, -2), (key3060, -2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

def rawRow18058 : Integer.Sparse Key := [(key3064, 6), (key3046, -2), (key3046, -2), (key3060, -2), (key3101, 6), (key3046, -2), (key3046, -2), (key3095, -2), (key3101, -2), (key3101, -2), (key3125, -2), (key3064, -2), (key3064, -2), (key3123, -2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

def rawRow18059 : Integer.Sparse Key := [(key3064, 6), (key3046, -2), (key3060, -2), (key3046, -2), (key3101, 6), (key3046, -2), (key3095, -2), (key3046, -2), (key3101, -2), (key3125, -2), (key3101, -2), (key3064, -2), (key3123, -2), (key3064, -2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

def rawRow18060 : Integer.Sparse Key := [(key3064, 6), (key3060, -2), (key3046, -2), (key3046, -2), (key3101, 6), (key3095, -2), (key3046, -2), (key3046, -2), (key3125, -2), (key3101, -2), (key3101, -2), (key3123, -2), (key3064, -2), (key3064, -2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

def rawRow18061 : Integer.Sparse Key := [(key3095, 6), (key3095, -2), (key3095, -2), (key3123, -2), (key3060, 6), (key3060, -2), (key3060, -2), (key3125, -2), (key3046, -2), (key3046, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

def rawRow18062 : Integer.Sparse Key := [(key3095, 6), (key3095, -2), (key3123, -2), (key3095, -2), (key3060, 6), (key3060, -2), (key3125, -2), (key3060, -2), (key3046, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, -2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

def rawRow18063 : Integer.Sparse Key := [(key3095, 6), (key3123, -2), (key3095, -2), (key3095, -2), (key3060, 6), (key3125, -2), (key3060, -2), (key3060, -2), (key3064, -2), (key3046, -2), (key3046, -2), (key3101, -2), (key3046, -2), (key3046, -2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

def rawRow18064 : Integer.Sparse Key := [(key3123, 6), (key3095, -2), (key3095, -2), (key3095, -2), (key3125, 6), (key3060, -2), (key3060, -2), (key3060, -2), (key3101, -2), (key3101, -2), (key3101, -2), (key3064, -2), (key3064, -2), (key3064, -2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

def rawRow18065 : Integer.Sparse Key := [(key3101, 6), (key3101, -2), (key3101, -2), (key3125, -2), (key3064, 6), (key3064, -2), (key3064, -2), (key3123, -2), (key3046, -2), (key3046, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

def rawRow18066 : Integer.Sparse Key := [(key3101, 6), (key3101, -2), (key3125, -2), (key3101, -2), (key3064, 6), (key3064, -2), (key3123, -2), (key3064, -2), (key3046, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, -2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

def rawRow18067 : Integer.Sparse Key := [(key3101, 6), (key3125, -2), (key3101, -2), (key3101, -2), (key3064, 6), (key3123, -2), (key3064, -2), (key3064, -2), (key3060, -2), (key3046, -2), (key3046, -2), (key3095, -2), (key3046, -2), (key3046, -2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

def rawRow18068 : Integer.Sparse Key := [(key3125, 6), (key3101, -2), (key3101, -2), (key3101, -2), (key3123, 6), (key3064, -2), (key3064, -2), (key3064, -2), (key3095, -2), (key3095, -2), (key3095, -2), (key3060, -2), (key3060, -2), (key3060, -2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

def rawRow18069 : Integer.Sparse Key := [(key1048, -2), (key1051, -2), (key1059, -2), (key1059, 6), (key1048, -2), (key1051, -2), (key1059, -2), (key1048, 2), (key1051, 2), (key1134, 2), (key1204, 2), (key1139, 2), (key1206, 2), (key1059, -2), (key1139, -2), (key1206, -2), (key1059, 6), (key1059, -2), (key1139, -2), (key1206, -2)]

def rawRow18070 : Integer.Sparse Key := [(key1051, -2), (key1048, -2), (key1059, -2), (key1059, 6), (key1051, -2), (key1048, -2), (key1059, -2), (key1051, 2), (key1048, 2), (key1204, 2), (key1134, 2), (key1206, 2), (key1139, 2), (key1059, -2), (key1206, -2), (key1139, -2), (key1059, 6), (key1059, -2), (key1206, -2), (key1139, -2)]

def rawRow18071 : Integer.Sparse Key := [(key1048, -2), (key1059, -2), (key1051, -2), (key1059, 6), (key1048, -2), (key1059, -2), (key1051, -2), (key1134, 2), (key1139, 2), (key1048, 2), (key1206, 2), (key1051, 2), (key1204, 2), (key1139, -2), (key1059, -2), (key1206, -2), (key1059, 6), (key1139, -2), (key1059, -2), (key1206, -2)]

def rawRow18072 : Integer.Sparse Key := [(key1059, -2), (key1048, -2), (key1051, -2), (key1059, 6), (key1059, -2), (key1048, -2), (key1051, -2), (key1139, 2), (key1134, 2), (key1206, 2), (key1048, 2), (key1204, 2), (key1051, 2), (key1139, -2), (key1206, -2), (key1059, -2), (key1059, 6), (key1139, -2), (key1206, -2), (key1059, -2)]

def rawRow18073 : Integer.Sparse Key := [(key1051, -2), (key1059, -2), (key1048, -2), (key1059, 6), (key1051, -2), (key1059, -2), (key1048, -2), (key1204, 2), (key1206, 2), (key1051, 2), (key1139, 2), (key1048, 2), (key1134, 2), (key1206, -2), (key1059, -2), (key1139, -2), (key1059, 6), (key1206, -2), (key1059, -2), (key1139, -2)]

def rawRow18074 : Integer.Sparse Key := [(key1059, -2), (key1051, -2), (key1048, -2), (key1059, 6), (key1059, -2), (key1051, -2), (key1048, -2), (key1206, 2), (key1204, 2), (key1139, 2), (key1051, 2), (key1134, 2), (key1048, 2), (key1206, -2), (key1139, -2), (key1059, -2), (key1059, 6), (key1206, -2), (key1139, -2), (key1059, -2)]

def rawRow18075 : Integer.Sparse Key := [(key1048, -2), (key1059, -2), (key1059, -2), (key1051, 6), (key1134, -2), (key1139, -2), (key1139, -2), (key1048, 2), (key1059, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1206, 2), (key1051, -2), (key1051, -2), (key1204, -2), (key1139, 6), (key1059, -2), (key1059, -2), (key1206, -2)]

def rawRow18076 : Integer.Sparse Key := [(key1059, -2), (key1048, -2), (key1059, -2), (key1051, 6), (key1139, -2), (key1134, -2), (key1139, -2), (key1059, 2), (key1048, 2), (key1206, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1051, -2), (key1204, -2), (key1051, -2), (key1139, 6), (key1059, -2), (key1206, -2), (key1059, -2)]

def rawRow18077 : Integer.Sparse Key := [(key1059, -2), (key1059, -2), (key1048, -2), (key1051, 6), (key1139, -2), (key1139, -2), (key1134, -2), (key1206, 2), (key1206, 2), (key1059, 2), (key1059, 2), (key1048, 2), (key1048, 2), (key1204, -2), (key1051, -2), (key1051, -2), (key1139, 6), (key1206, -2), (key1059, -2), (key1059, -2)]

def rawRow18078 : Integer.Sparse Key := [(key1051, -2), (key1059, -2), (key1059, -2), (key1048, 6), (key1204, -2), (key1206, -2), (key1206, -2), (key1051, 2), (key1059, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1139, 2), (key1048, -2), (key1048, -2), (key1134, -2), (key1206, 6), (key1059, -2), (key1059, -2), (key1139, -2)]

def rawRow18079 : Integer.Sparse Key := [(key1059, -2), (key1051, -2), (key1059, -2), (key1048, 6), (key1206, -2), (key1204, -2), (key1206, -2), (key1059, 2), (key1051, 2), (key1139, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1048, -2), (key1134, -2), (key1048, -2), (key1206, 6), (key1059, -2), (key1139, -2), (key1059, -2)]

def rawRow18080 : Integer.Sparse Key := [(key1059, -2), (key1059, -2), (key1051, -2), (key1048, 6), (key1206, -2), (key1206, -2), (key1204, -2), (key1139, 2), (key1139, 2), (key1059, 2), (key1059, 2), (key1051, 2), (key1051, 2), (key1134, -2), (key1048, -2), (key1048, -2), (key1206, 6), (key1139, -2), (key1059, -2), (key1059, -2)]

def rawRow18081 : Integer.Sparse Key := [(key1134, -2), (key1139, -2), (key1139, -2), (key1139, 6), (key1048, -2), (key1059, -2), (key1059, -2), (key1048, 2), (key1059, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1206, 2), (key1059, -2), (key1059, -2), (key1206, -2), (key1051, 6), (key1051, -2), (key1051, -2), (key1204, -2)]

def rawRow18082 : Integer.Sparse Key := [(key1139, -2), (key1134, -2), (key1139, -2), (key1139, 6), (key1059, -2), (key1048, -2), (key1059, -2), (key1059, 2), (key1048, 2), (key1206, 2), (key1048, 2), (key1206, 2), (key1059, 2), (key1059, -2), (key1206, -2), (key1059, -2), (key1051, 6), (key1051, -2), (key1204, -2), (key1051, -2)]

def rawRow18083 : Integer.Sparse Key := [(key1139, -2), (key1139, -2), (key1134, -2), (key1139, 6), (key1059, -2), (key1059, -2), (key1048, -2), (key1206, 2), (key1206, 2), (key1059, 2), (key1059, 2), (key1048, 2), (key1048, 2), (key1206, -2), (key1059, -2), (key1059, -2), (key1051, 6), (key1204, -2), (key1051, -2), (key1051, -2)]

def rawRow18084 : Integer.Sparse Key := [(key1139, -2), (key1139, -2), (key1139, -2), (key1134, 6), (key1206, -2), (key1206, -2), (key1206, -2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1048, -2), (key1048, -2), (key1048, -2), (key1204, 6), (key1051, -2), (key1051, -2), (key1051, -2)]

def rawRow18085 : Integer.Sparse Key := [(key1204, -2), (key1206, -2), (key1206, -2), (key1206, 6), (key1051, -2), (key1059, -2), (key1059, -2), (key1051, 2), (key1059, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1139, 2), (key1059, -2), (key1059, -2), (key1139, -2), (key1048, 6), (key1048, -2), (key1048, -2), (key1134, -2)]

def rawRow18086 : Integer.Sparse Key := [(key1206, -2), (key1204, -2), (key1206, -2), (key1206, 6), (key1059, -2), (key1051, -2), (key1059, -2), (key1059, 2), (key1051, 2), (key1139, 2), (key1051, 2), (key1139, 2), (key1059, 2), (key1059, -2), (key1139, -2), (key1059, -2), (key1048, 6), (key1048, -2), (key1134, -2), (key1048, -2)]

def rawRow18087 : Integer.Sparse Key := [(key1206, -2), (key1206, -2), (key1204, -2), (key1206, 6), (key1059, -2), (key1059, -2), (key1051, -2), (key1139, 2), (key1139, 2), (key1059, 2), (key1059, 2), (key1051, 2), (key1051, 2), (key1139, -2), (key1059, -2), (key1059, -2), (key1048, 6), (key1134, -2), (key1048, -2), (key1048, -2)]

def rawRow18088 : Integer.Sparse Key := [(key1206, -2), (key1206, -2), (key1206, -2), (key1204, 6), (key1139, -2), (key1139, -2), (key1139, -2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1059, 2), (key1051, -2), (key1051, -2), (key1051, -2), (key1134, 6), (key1048, -2), (key1048, -2), (key1048, -2)]

def rawRow18089 : Integer.Sparse Key := [(key1056, 4), (key1144, 4), (key1208, 4), (key1064, -2), (key1065, -2), (key1144, -2), (key1208, -2), (key1158, -2), (key1215, -2), (key1064, -2), (key1065, -2), (key1144, -2), (key1208, -2), (key1158, -2), (key1215, -2), (key1079, 4), (key1158, 4), (key1215, 4)]

def rawRow18090 : Integer.Sparse Key := [(key1056, 4), (key1208, 4), (key1144, 4), (key1065, -2), (key1064, -2), (key1208, -2), (key1144, -2), (key1215, -2), (key1158, -2), (key1065, -2), (key1064, -2), (key1208, -2), (key1144, -2), (key1215, -2), (key1158, -2), (key1079, 4), (key1215, 4), (key1158, 4)]

def rawRow18091 : Integer.Sparse Key := [(key1144, 4), (key1056, 4), (key1208, 4), (key1144, -2), (key1158, -2), (key1064, -2), (key1215, -2), (key1065, -2), (key1208, -2), (key1144, -2), (key1158, -2), (key1064, -2), (key1215, -2), (key1065, -2), (key1208, -2), (key1158, 4), (key1079, 4), (key1215, 4)]

def rawRow18092 : Integer.Sparse Key := [(key1144, 4), (key1208, 4), (key1056, 4), (key1158, -2), (key1144, -2), (key1215, -2), (key1064, -2), (key1208, -2), (key1065, -2), (key1158, -2), (key1144, -2), (key1215, -2), (key1064, -2), (key1208, -2), (key1065, -2), (key1158, 4), (key1215, 4), (key1079, 4)]

def rawRow18093 : Integer.Sparse Key := [(key1208, 4), (key1056, 4), (key1144, 4), (key1208, -2), (key1215, -2), (key1065, -2), (key1158, -2), (key1064, -2), (key1144, -2), (key1208, -2), (key1215, -2), (key1065, -2), (key1158, -2), (key1064, -2), (key1144, -2), (key1215, 4), (key1079, 4), (key1158, 4)]

def rawRow18094 : Integer.Sparse Key := [(key1208, 4), (key1144, 4), (key1056, 4), (key1215, -2), (key1208, -2), (key1158, -2), (key1065, -2), (key1144, -2), (key1064, -2), (key1215, -2), (key1208, -2), (key1158, -2), (key1065, -2), (key1144, -2), (key1064, -2), (key1215, 4), (key1158, 4), (key1079, 4)]

def rawRow18095 : Integer.Sparse Key := [(key1064, 4), (key1064, 4), (key1215, 4), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1064, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1215, -2), (key1065, 4), (key1065, 4), (key1208, 4)]

def rawRow18096 : Integer.Sparse Key := [(key1064, 4), (key1215, 4), (key1064, 4), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1065, 4), (key1208, 4), (key1065, 4)]

def rawRow18097 : Integer.Sparse Key := [(key1215, 4), (key1064, 4), (key1064, 4), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1215, -2), (key1215, -2), (key1079, -2), (key1079, -2), (key1064, -2), (key1064, -2), (key1208, 4), (key1065, 4), (key1065, 4)]

def rawRow18098 : Integer.Sparse Key := [(key1065, 4), (key1065, 4), (key1158, 4), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1065, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1158, -2), (key1064, 4), (key1064, 4), (key1144, 4)]

def rawRow18099 : Integer.Sparse Key := [(key1065, 4), (key1158, 4), (key1065, 4), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1064, 4), (key1144, 4), (key1064, 4)]

def rawRow18100 : Integer.Sparse Key := [(key1158, 4), (key1065, 4), (key1065, 4), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1158, -2), (key1158, -2), (key1079, -2), (key1079, -2), (key1065, -2), (key1065, -2), (key1144, 4), (key1064, 4), (key1064, 4)]

def rawRow18101 : Integer.Sparse Key := [(key1064, 4), (key1064, 4), (key1215, 4), (key1064, -2), (key1079, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1215, -2), (key1056, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1208, -2), (key1065, 4), (key1065, 4), (key1208, 4)]

def rawRow18102 : Integer.Sparse Key := [(key1064, 4), (key1215, 4), (key1064, 4), (key1079, -2), (key1064, -2), (key1215, -2), (key1064, -2), (key1215, -2), (key1079, -2), (key1065, -2), (key1056, -2), (key1208, -2), (key1056, -2), (key1208, -2), (key1065, -2), (key1065, 4), (key1208, 4), (key1065, 4)]

def rawRow18103 : Integer.Sparse Key := [(key1215, 4), (key1064, 4), (key1064, 4), (key1215, -2), (key1215, -2), (key1079, -2), (key1079, -2), (key1064, -2), (key1064, -2), (key1208, -2), (key1208, -2), (key1065, -2), (key1065, -2), (key1056, -2), (key1056, -2), (key1208, 4), (key1065, 4), (key1065, 4)]

def rawRow18104 : Integer.Sparse Key := [(key1079, 4), (key1079, 4), (key1079, 4), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1056, 4), (key1056, 4), (key1056, 4)]

def rawRow18105 : Integer.Sparse Key := [(key1065, 4), (key1065, 4), (key1158, 4), (key1065, -2), (key1079, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1158, -2), (key1056, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1144, -2), (key1064, 4), (key1064, 4), (key1144, 4)]

def rawRow18106 : Integer.Sparse Key := [(key1065, 4), (key1158, 4), (key1065, 4), (key1079, -2), (key1065, -2), (key1158, -2), (key1065, -2), (key1158, -2), (key1079, -2), (key1064, -2), (key1056, -2), (key1144, -2), (key1056, -2), (key1144, -2), (key1064, -2), (key1064, 4), (key1144, 4), (key1064, 4)]

def rawRow18107 : Integer.Sparse Key := [(key1158, 4), (key1065, 4), (key1065, 4), (key1158, -2), (key1158, -2), (key1079, -2), (key1079, -2), (key1065, -2), (key1065, -2), (key1144, -2), (key1144, -2), (key1064, -2), (key1064, -2), (key1056, -2), (key1056, -2), (key1144, 4), (key1064, 4), (key1064, 4)]

def rawRow18108 : Integer.Sparse Key := [(key1079, 4), (key1079, 4), (key1079, 4), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1065, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1064, -2), (key1056, 4), (key1056, 4), (key1056, 4)]

def rawRow18109 : Integer.Sparse Key := [(key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2690, 2), (key2819, 2), (key2956, 2), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2711, 2), (key2741, 2), (key2814, 2), (key2954, 2), (key2901, 2), (key2980, 2), (key2716, -1), (key2743, -1), (key2819, -1), (key2956, -1), (key2901, -1), (key2980, -1), (key2690, 2), (key2819, 2), (key2956, 2), (key2716, -1), (key2743, -1), (key2819, -1), (key2956, -1), (key2901, -1), (key2980, -1)]

def rawRow18110 : Integer.Sparse Key := [(key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2690, 2), (key2956, 2), (key2819, 2), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2741, 2), (key2711, 2), (key2954, 2), (key2814, 2), (key2980, 2), (key2901, 2), (key2743, -1), (key2716, -1), (key2956, -1), (key2819, -1), (key2980, -1), (key2901, -1), (key2690, 2), (key2956, 2), (key2819, 2), (key2743, -1), (key2716, -1), (key2956, -1), (key2819, -1), (key2980, -1), (key2901, -1)]

def rawRow18111 : Integer.Sparse Key := [(key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2819, 2), (key2690, 2), (key2956, 2), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2814, 2), (key2901, 2), (key2711, 2), (key2980, 2), (key2741, 2), (key2954, 2), (key2819, -1), (key2901, -1), (key2716, -1), (key2980, -1), (key2743, -1), (key2956, -1), (key2819, 2), (key2690, 2), (key2956, 2), (key2819, -1), (key2901, -1), (key2716, -1), (key2980, -1), (key2743, -1), (key2956, -1)]

def rawRow18112 : Integer.Sparse Key := [(key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2819, 2), (key2956, 2), (key2690, 2), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2901, 2), (key2814, 2), (key2980, 2), (key2711, 2), (key2954, 2), (key2741, 2), (key2901, -1), (key2819, -1), (key2980, -1), (key2716, -1), (key2956, -1), (key2743, -1), (key2819, 2), (key2956, 2), (key2690, 2), (key2901, -1), (key2819, -1), (key2980, -1), (key2716, -1), (key2956, -1), (key2743, -1)]

def rawRow18113 : Integer.Sparse Key := [(key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2956, 2), (key2690, 2), (key2819, 2), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2954, 2), (key2980, 2), (key2741, 2), (key2901, 2), (key2711, 2), (key2814, 2), (key2956, -1), (key2980, -1), (key2743, -1), (key2901, -1), (key2716, -1), (key2819, -1), (key2956, 2), (key2690, 2), (key2819, 2), (key2956, -1), (key2980, -1), (key2743, -1), (key2901, -1), (key2716, -1), (key2819, -1)]

def rawRow18114 : Integer.Sparse Key := [(key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2956, 2), (key2819, 2), (key2690, 2), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2980, 2), (key2954, 2), (key2901, 2), (key2741, 2), (key2814, 2), (key2711, 2), (key2980, -1), (key2956, -1), (key2901, -1), (key2743, -1), (key2819, -1), (key2716, -1), (key2956, 2), (key2819, 2), (key2690, 2), (key2980, -1), (key2956, -1), (key2901, -1), (key2743, -1), (key2819, -1), (key2716, -1)]

def rawRow18115 : Integer.Sparse Key := [(key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2683, 2), (key2683, 2), (key2954, 2), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2), (key2683, -1), (key2741, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2954, -1), (key2716, 2), (key2716, 2), (key2980, 2), (key2690, -1), (key2743, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2956, -1)]

def rawRow18116 : Integer.Sparse Key := [(key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2683, 2), (key2954, 2), (key2683, 2), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2741, -1), (key2683, -1), (key2954, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2716, 2), (key2980, 2), (key2716, 2), (key2743, -1), (key2690, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2743, -1)]

def rawRow18117 : Integer.Sparse Key := [(key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2954, 2), (key2683, 2), (key2683, 2), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2), (key2954, -1), (key2954, -1), (key2741, -1), (key2741, -1), (key2683, -1), (key2683, -1), (key2980, 2), (key2716, 2), (key2716, 2), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1)]

def rawRow18118 : Integer.Sparse Key := [(key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2680, 2), (key2680, 2), (key2814, 2), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2), (key2680, -1), (key2711, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2814, -1), (key2743, 2), (key2743, 2), (key2901, 2), (key2690, -1), (key2716, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2819, -1)]

def rawRow18119 : Integer.Sparse Key := [(key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2680, 2), (key2814, 2), (key2680, 2), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2711, -1), (key2680, -1), (key2814, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2743, 2), (key2901, 2), (key2743, 2), (key2716, -1), (key2690, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2716, -1)]

def rawRow18120 : Integer.Sparse Key := [(key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2814, 2), (key2680, 2), (key2680, 2), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2), (key2814, -1), (key2814, -1), (key2711, -1), (key2711, -1), (key2680, -1), (key2680, -1), (key2901, 2), (key2743, 2), (key2743, 2), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1)]

def rawRow18121 : Integer.Sparse Key := [(key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2716, 2), (key2716, 2), (key2980, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2), (key2690, -1), (key2743, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2956, -1), (key2683, 2), (key2683, 2), (key2954, 2), (key2683, -1), (key2741, -1), (key2683, -1), (key2954, -1), (key2741, -1), (key2954, -1)]

def rawRow18122 : Integer.Sparse Key := [(key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2716, 2), (key2980, 2), (key2716, 2), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2743, -1), (key2690, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2743, -1), (key2683, 2), (key2954, 2), (key2683, 2), (key2741, -1), (key2683, -1), (key2954, -1), (key2683, -1), (key2954, -1), (key2741, -1)]

def rawRow18123 : Integer.Sparse Key := [(key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2980, 2), (key2716, 2), (key2716, 2), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2954, 2), (key2683, 2), (key2683, 2), (key2954, -1), (key2954, -1), (key2741, -1), (key2741, -1), (key2683, -1), (key2683, -1)]

def rawRow18124 : Integer.Sparse Key := [(key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2711, 2), (key2711, 2), (key2711, 2), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2741, 2), (key2741, 2), (key2741, 2), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1)]

def rawRow18125 : Integer.Sparse Key := [(key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2743, 2), (key2743, 2), (key2901, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2), (key2690, -1), (key2716, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2819, -1), (key2680, 2), (key2680, 2), (key2814, 2), (key2680, -1), (key2711, -1), (key2680, -1), (key2814, -1), (key2711, -1), (key2814, -1)]

def rawRow18126 : Integer.Sparse Key := [(key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2743, 2), (key2901, 2), (key2743, 2), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2716, -1), (key2690, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2716, -1), (key2680, 2), (key2814, 2), (key2680, 2), (key2711, -1), (key2680, -1), (key2814, -1), (key2680, -1), (key2814, -1), (key2711, -1)]

def rawRow18127 : Integer.Sparse Key := [(key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2901, 2), (key2743, 2), (key2743, 2), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2814, 2), (key2680, 2), (key2680, 2), (key2814, -1), (key2814, -1), (key2711, -1), (key2711, -1), (key2680, -1), (key2680, -1)]

def rawRow18128 : Integer.Sparse Key := [(key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2741, 2), (key2741, 2), (key2741, 2), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2683, -1), (key2711, 2), (key2711, 2), (key2711, 2), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1), (key2680, -1)]

def rawRow18129 : Integer.Sparse Key := [(key3080, 4), (key3085, 4), (key3087, 4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3100, 12)]

def rawRow18130 : Integer.Sparse Key := [(key3080, 4), (key3087, 4), (key3085, 4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3100, 12)]

def rawRow18131 : Integer.Sparse Key := [(key3085, 4), (key3080, 4), (key3087, 4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3100, 12)]

def rawRow18132 : Integer.Sparse Key := [(key3085, 4), (key3087, 4), (key3080, 4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, 12)]

def rawRow18133 : Integer.Sparse Key := [(key3087, 4), (key3080, 4), (key3085, 4), (key3087, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3100, 12)]

def rawRow18134 : Integer.Sparse Key := [(key3087, 4), (key3085, 4), (key3080, 4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3100, 12)]

def rawRow18135 : Integer.Sparse Key := [(key3085, 4), (key3085, 4), (key3100, 4), (key3080, -4), (key3087, -4), (key3087, -4), (key3085, -4), (key3100, -4), (key3100, -4), (key3087, 12)]

def rawRow18136 : Integer.Sparse Key := [(key3085, 4), (key3100, 4), (key3085, 4), (key3087, -4), (key3080, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, 12)]

def rawRow18137 : Integer.Sparse Key := [(key3100, 4), (key3085, 4), (key3085, 4), (key3087, -4), (key3087, -4), (key3080, -4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, 12)]

def rawRow18138 : Integer.Sparse Key := [(key3087, 4), (key3087, 4), (key3100, 4), (key3080, -4), (key3085, -4), (key3085, -4), (key3087, -4), (key3100, -4), (key3100, -4), (key3085, 12)]

def rawRow18139 : Integer.Sparse Key := [(key3087, 4), (key3100, 4), (key3087, 4), (key3085, -4), (key3080, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, 12)]

def rawRow18140 : Integer.Sparse Key := [(key3100, 4), (key3087, 4), (key3087, 4), (key3085, -4), (key3085, -4), (key3080, -4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, 12)]

def rawRow18141 : Integer.Sparse Key := [(key3085, 4), (key3085, 4), (key3100, 4), (key3085, -4), (key3100, -4), (key3100, -4), (key3080, -4), (key3087, -4), (key3087, -4), (key3087, 12)]

def rawRow18142 : Integer.Sparse Key := [(key3085, 4), (key3100, 4), (key3085, 4), (key3100, -4), (key3085, -4), (key3100, -4), (key3087, -4), (key3080, -4), (key3087, -4), (key3087, 12)]

def rawRow18143 : Integer.Sparse Key := [(key3100, 4), (key3085, 4), (key3085, 4), (key3100, -4), (key3100, -4), (key3085, -4), (key3087, -4), (key3087, -4), (key3080, -4), (key3087, 12)]

def rawRow18144 : Integer.Sparse Key := [(key3100, 4), (key3100, 4), (key3100, 4), (key3085, -4), (key3085, -4), (key3085, -4), (key3087, -4), (key3087, -4), (key3087, -4), (key3080, 12)]

def rawRow18145 : Integer.Sparse Key := [(key3087, 4), (key3087, 4), (key3100, 4), (key3087, -4), (key3100, -4), (key3100, -4), (key3080, -4), (key3085, -4), (key3085, -4), (key3085, 12)]

def rawRow18146 : Integer.Sparse Key := [(key3087, 4), (key3100, 4), (key3087, 4), (key3100, -4), (key3087, -4), (key3100, -4), (key3085, -4), (key3080, -4), (key3085, -4), (key3085, 12)]

def rawRow18147 : Integer.Sparse Key := [(key3100, 4), (key3087, 4), (key3087, 4), (key3100, -4), (key3100, -4), (key3087, -4), (key3085, -4), (key3085, -4), (key3080, -4), (key3085, 12)]

def rawRow18148 : Integer.Sparse Key := [(key3100, 4), (key3100, 4), (key3100, 4), (key3087, -4), (key3087, -4), (key3087, -4), (key3085, -4), (key3085, -4), (key3085, -4), (key3080, 12)]

def rawRow18149 : Integer.Sparse Key := [(key2414, -2), (key2417, -2), (key2424, -2), (key2424, 6), (key3033, -2), (key3035, -2), (key3039, -2), (key3033, 2), (key3035, 2), (key3120, 2), (key3128, 2), (key3131, 2), (key3138, 2), (key3039, -2), (key3131, -2), (key3138, -2), (key3039, 6), (key3039, -2), (key3131, -2), (key3138, -2)]

def rawRow18150 : Integer.Sparse Key := [(key2417, -2), (key2414, -2), (key2424, -2), (key2424, 6), (key3035, -2), (key3033, -2), (key3039, -2), (key3035, 2), (key3033, 2), (key3128, 2), (key3120, 2), (key3138, 2), (key3131, 2), (key3039, -2), (key3138, -2), (key3131, -2), (key3039, 6), (key3039, -2), (key3138, -2), (key3131, -2)]

def rawRow18151 : Integer.Sparse Key := [(key2414, -2), (key2424, -2), (key2417, -2), (key2424, 6), (key3033, -2), (key3039, -2), (key3035, -2), (key3120, 2), (key3131, 2), (key3033, 2), (key3138, 2), (key3035, 2), (key3128, 2), (key3131, -2), (key3039, -2), (key3138, -2), (key3039, 6), (key3131, -2), (key3039, -2), (key3138, -2)]

def rawRow18152 : Integer.Sparse Key := [(key2424, -2), (key2414, -2), (key2417, -2), (key2424, 6), (key3039, -2), (key3033, -2), (key3035, -2), (key3131, 2), (key3120, 2), (key3138, 2), (key3033, 2), (key3128, 2), (key3035, 2), (key3131, -2), (key3138, -2), (key3039, -2), (key3039, 6), (key3131, -2), (key3138, -2), (key3039, -2)]

def rawRow18153 : Integer.Sparse Key := [(key2417, -2), (key2424, -2), (key2414, -2), (key2424, 6), (key3035, -2), (key3039, -2), (key3033, -2), (key3128, 2), (key3138, 2), (key3035, 2), (key3131, 2), (key3033, 2), (key3120, 2), (key3138, -2), (key3039, -2), (key3131, -2), (key3039, 6), (key3138, -2), (key3039, -2), (key3131, -2)]

def rawRow18154 : Integer.Sparse Key := [(key2424, -2), (key2417, -2), (key2414, -2), (key2424, 6), (key3039, -2), (key3035, -2), (key3033, -2), (key3138, 2), (key3128, 2), (key3131, 2), (key3035, 2), (key3120, 2), (key3033, 2), (key3138, -2), (key3131, -2), (key3039, -2), (key3039, 6), (key3138, -2), (key3131, -2), (key3039, -2)]

def rawRow18155 : Integer.Sparse Key := [(key2414, -2), (key2424, -2), (key2424, -2), (key2417, 6), (key3120, -2), (key3131, -2), (key3131, -2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3035, -2), (key3035, -2), (key3128, -2), (key3131, 6), (key3039, -2), (key3039, -2), (key3138, -2)]

def rawRow18156 : Integer.Sparse Key := [(key2424, -2), (key2414, -2), (key2424, -2), (key2417, 6), (key3131, -2), (key3120, -2), (key3131, -2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3035, -2), (key3128, -2), (key3035, -2), (key3131, 6), (key3039, -2), (key3138, -2), (key3039, -2)]

def rawRow18157 : Integer.Sparse Key := [(key2424, -2), (key2424, -2), (key2414, -2), (key2417, 6), (key3131, -2), (key3131, -2), (key3120, -2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3128, -2), (key3035, -2), (key3035, -2), (key3131, 6), (key3138, -2), (key3039, -2), (key3039, -2)]

def rawRow18158 : Integer.Sparse Key := [(key2417, -2), (key2424, -2), (key2424, -2), (key2414, 6), (key3128, -2), (key3138, -2), (key3138, -2), (key3035, 2), (key3039, 2), (key3035, 2), (key3131, 2), (key3039, 2), (key3131, 2), (key3033, -2), (key3033, -2), (key3120, -2), (key3138, 6), (key3039, -2), (key3039, -2), (key3131, -2)]

def rawRow18159 : Integer.Sparse Key := [(key2424, -2), (key2417, -2), (key2424, -2), (key2414, 6), (key3138, -2), (key3128, -2), (key3138, -2), (key3039, 2), (key3035, 2), (key3131, 2), (key3035, 2), (key3131, 2), (key3039, 2), (key3033, -2), (key3120, -2), (key3033, -2), (key3138, 6), (key3039, -2), (key3131, -2), (key3039, -2)]

def rawRow18160 : Integer.Sparse Key := [(key2424, -2), (key2424, -2), (key2417, -2), (key2414, 6), (key3138, -2), (key3138, -2), (key3128, -2), (key3131, 2), (key3131, 2), (key3039, 2), (key3039, 2), (key3035, 2), (key3035, 2), (key3120, -2), (key3033, -2), (key3033, -2), (key3138, 6), (key3131, -2), (key3039, -2), (key3039, -2)]

def rawRow18161 : Integer.Sparse Key := [(key2487, -2), (key2492, -2), (key2492, -2), (key2492, 6), (key2414, -2), (key2424, -2), (key2424, -2), (key3033, 2), (key3039, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3138, 2), (key3039, -2), (key3039, -2), (key3138, -2), (key3035, 6), (key3035, -2), (key3035, -2), (key3128, -2)]

def rawRow18162 : Integer.Sparse Key := [(key2492, -2), (key2487, -2), (key2492, -2), (key2492, 6), (key2424, -2), (key2414, -2), (key2424, -2), (key3039, 2), (key3033, 2), (key3138, 2), (key3033, 2), (key3138, 2), (key3039, 2), (key3039, -2), (key3138, -2), (key3039, -2), (key3035, 6), (key3035, -2), (key3128, -2), (key3035, -2)]

def rawRow18163 : Integer.Sparse Key := [(key2492, -2), (key2492, -2), (key2487, -2), (key2492, 6), (key2424, -2), (key2424, -2), (key2414, -2), (key3138, 2), (key3138, 2), (key3039, 2), (key3039, 2), (key3033, 2), (key3033, 2), (key3138, -2), (key3039, -2), (key3039, -2), (key3035, 6), (key3128, -2), (key3035, -2), (key3035, -2)]

def rawRow18164 : Integer.Sparse Key := [(key2492, -2), (key2492, -2), (key2492, -2), (key2487, 6), (key2548, -2), (key2548, -2), (key2548, -2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2414, -2), (key3033, -2), (key3033, -2), (key3128, 6), (key3035, -2), (key3035, -2), (key3035, -2)]

def rawRow18165 : Integer.Sparse Key := [(key2546, -2), (key2548, -2), (key2548, -2), (key2548, 6), (key2417, -2), (key2424, -2), (key2424, -2), (key2417, 2), (key2424, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2492, 2), (key2424, -2), (key2424, -2), (key2492, -2), (key2414, 6), (key3033, -2), (key3033, -2), (key3120, -2)]

def rawRow18166 : Integer.Sparse Key := [(key2548, -2), (key2546, -2), (key2548, -2), (key2548, 6), (key2424, -2), (key2417, -2), (key2424, -2), (key2424, 2), (key2417, 2), (key2492, 2), (key2417, 2), (key2492, 2), (key2424, 2), (key2424, -2), (key2492, -2), (key2424, -2), (key2414, 6), (key3033, -2), (key3120, -2), (key3033, -2)]

def rawRow18167 : Integer.Sparse Key := [(key2548, -2), (key2548, -2), (key2546, -2), (key2548, 6), (key2424, -2), (key2424, -2), (key2417, -2), (key2492, 2), (key2492, 2), (key2424, 2), (key2424, 2), (key2417, 2), (key2417, 2), (key2492, -2), (key2424, -2), (key2424, -2), (key2414, 6), (key3120, -2), (key3033, -2), (key3033, -2)]

def rawRow18168 : Integer.Sparse Key := [(key2548, -2), (key2548, -2), (key2548, -2), (key2546, 6), (key2492, -2), (key2492, -2), (key2492, -2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2424, 2), (key2417, -2), (key2417, -2), (key2417, -2), (key2487, 6), (key2414, -2), (key3033, -2), (key3033, -2)]

def rawRow18169 : Integer.Sparse Key := [(key2101, 4), (key2106, 4), (key2111, 4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2139, 12)]

def rawRow18170 : Integer.Sparse Key := [(key2101, 4), (key2111, 4), (key2106, 4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2139, 12)]

def rawRow18171 : Integer.Sparse Key := [(key2106, 4), (key2101, 4), (key2111, 4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2139, 12)]

def rawRow18172 : Integer.Sparse Key := [(key2106, 4), (key2111, 4), (key2101, 4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, 12)]

def rawRow18173 : Integer.Sparse Key := [(key2111, 4), (key2101, 4), (key2106, 4), (key2111, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2139, 12)]

def rawRow18174 : Integer.Sparse Key := [(key2111, 4), (key2106, 4), (key2101, 4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2139, 12)]

def rawRow18175 : Integer.Sparse Key := [(key2106, 4), (key2106, 4), (key2139, 4), (key2101, -4), (key2111, -4), (key2111, -4), (key2106, -4), (key2139, -4), (key2139, -4), (key2111, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18176 : Integer.Sparse Key := [(key2106, 4), (key2139, 4), (key2106, 4), (key2111, -4), (key2101, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2139, -4), (key2111, 12)]

def rawRow18177 : Integer.Sparse Key := [(key2139, 4), (key2106, 4), (key2106, 4), (key2111, -4), (key2111, -4), (key2101, -4), (key2139, -4), (key2139, -4), (key2106, -4), (key2111, 12)]

def rawRow18178 : Integer.Sparse Key := [(key2111, 4), (key2111, 4), (key2139, 4), (key2101, -4), (key2106, -4), (key2106, -4), (key2111, -4), (key2139, -4), (key2139, -4), (key2106, 12)]

def rawRow18179 : Integer.Sparse Key := [(key2111, 4), (key2139, 4), (key2111, 4), (key2106, -4), (key2101, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2139, -4), (key2106, 12)]

def rawRow18180 : Integer.Sparse Key := [(key2139, 4), (key2111, 4), (key2111, 4), (key2106, -4), (key2106, -4), (key2101, -4), (key2139, -4), (key2139, -4), (key2111, -4), (key2106, 12)]

def rawRow18181 : Integer.Sparse Key := [(key2106, 4), (key2106, 4), (key2139, 4), (key2106, -4), (key2139, -4), (key2139, -4), (key2101, -4), (key2111, -4), (key2111, -4), (key2111, 12)]

def rawRow18182 : Integer.Sparse Key := [(key2106, 4), (key2139, 4), (key2106, 4), (key2139, -4), (key2106, -4), (key2139, -4), (key2111, -4), (key2101, -4), (key2111, -4), (key2111, 12)]

def rawRow18183 : Integer.Sparse Key := [(key2139, 4), (key2106, 4), (key2106, 4), (key2139, -4), (key2139, -4), (key2106, -4), (key2111, -4), (key2111, -4), (key2101, -4), (key2111, 12)]

def rawRow18184 : Integer.Sparse Key := [(key2139, 4), (key2139, 4), (key2139, 4), (key2106, -4), (key2106, -4), (key2106, -4), (key2111, -4), (key2111, -4), (key2111, -4), (key2101, 12)]

def rawRow18185 : Integer.Sparse Key := [(key2111, 4), (key2111, 4), (key2139, 4), (key2111, -4), (key2139, -4), (key2139, -4), (key2101, -4), (key2106, -4), (key2106, -4), (key2106, 12)]

def rawRow18186 : Integer.Sparse Key := [(key2111, 4), (key2139, 4), (key2111, 4), (key2139, -4), (key2111, -4), (key2139, -4), (key2106, -4), (key2101, -4), (key2106, -4), (key2106, 12)]

def rawRow18187 : Integer.Sparse Key := [(key2139, 4), (key2111, 4), (key2111, 4), (key2139, -4), (key2139, -4), (key2111, -4), (key2106, -4), (key2106, -4), (key2101, -4), (key2106, 12)]

def rawRow18188 : Integer.Sparse Key := [(key2139, 4), (key2139, 4), (key2139, 4), (key2111, -4), (key2111, -4), (key2111, -4), (key2106, -4), (key2106, -4), (key2106, -4), (key2101, 12)]

def rawRow18189 : Integer.Sparse Key := [(key3047, -1), (key3050, -1), (key3096, -1), (key3103, -1), (key3106, -1), (key3110, -1), (key3054, 2), (key3106, 2), (key3110, 2), (key3047, -1), (key3050, -1), (key3096, -1), (key3103, -1), (key3106, -1), (key3110, -1), (key3061, 2), (key3066, 2), (key3096, 2), (key3103, 2), (key3134, 2), (key3136, 2), (key3069, -1), (key3072, -1), (key3106, -1), (key3110, -1), (key3134, -1), (key3136, -1), (key3054, 2), (key3106, 2), (key3110, 2), (key3069, -1), (key3072, -1), (key3106, -1), (key3110, -1), (key3134, -1), (key3136, -1)]

def rawRow18190 : Integer.Sparse Key := [(key3050, -1), (key3047, -1), (key3103, -1), (key3096, -1), (key3110, -1), (key3106, -1), (key3054, 2), (key3110, 2), (key3106, 2), (key3050, -1), (key3047, -1), (key3103, -1), (key3096, -1), (key3110, -1), (key3106, -1), (key3066, 2), (key3061, 2), (key3103, 2), (key3096, 2), (key3136, 2), (key3134, 2), (key3072, -1), (key3069, -1), (key3110, -1), (key3106, -1), (key3136, -1), (key3134, -1), (key3054, 2), (key3110, 2), (key3106, 2), (key3072, -1), (key3069, -1), (key3110, -1), (key3106, -1), (key3136, -1), (key3134, -1)]

def rawRow18191 : Integer.Sparse Key := [(key3096, -1), (key3106, -1), (key3047, -1), (key3110, -1), (key3050, -1), (key3103, -1), (key3106, 2), (key3054, 2), (key3110, 2), (key3096, -1), (key3106, -1), (key3047, -1), (key3110, -1), (key3050, -1), (key3103, -1), (key3096, 2), (key3134, 2), (key3061, 2), (key3136, 2), (key3066, 2), (key3103, 2), (key3106, -1), (key3134, -1), (key3069, -1), (key3136, -1), (key3072, -1), (key3110, -1), (key3106, 2), (key3054, 2), (key3110, 2), (key3106, -1), (key3134, -1), (key3069, -1), (key3136, -1), (key3072, -1), (key3110, -1)]

def rawRow18192 : Integer.Sparse Key := [(key3106, -1), (key3096, -1), (key3110, -1), (key3047, -1), (key3103, -1), (key3050, -1), (key3106, 2), (key3110, 2), (key3054, 2), (key3106, -1), (key3096, -1), (key3110, -1), (key3047, -1), (key3103, -1), (key3050, -1), (key3134, 2), (key3096, 2), (key3136, 2), (key3061, 2), (key3103, 2), (key3066, 2), (key3134, -1), (key3106, -1), (key3136, -1), (key3069, -1), (key3110, -1), (key3072, -1), (key3106, 2), (key3110, 2), (key3054, 2), (key3134, -1), (key3106, -1), (key3136, -1), (key3069, -1), (key3110, -1), (key3072, -1)]

def rawRow18193 : Integer.Sparse Key := [(key3103, -1), (key3110, -1), (key3050, -1), (key3106, -1), (key3047, -1), (key3096, -1), (key3110, 2), (key3054, 2), (key3106, 2), (key3103, -1), (key3110, -1), (key3050, -1), (key3106, -1), (key3047, -1), (key3096, -1), (key3103, 2), (key3136, 2), (key3066, 2), (key3134, 2), (key3061, 2), (key3096, 2), (key3110, -1), (key3136, -1), (key3072, -1), (key3134, -1), (key3069, -1), (key3106, -1), (key3110, 2), (key3054, 2), (key3106, 2), (key3110, -1), (key3136, -1), (key3072, -1), (key3134, -1), (key3069, -1), (key3106, -1)]

def rawRow18194 : Integer.Sparse Key := [(key3110, -1), (key3103, -1), (key3106, -1), (key3050, -1), (key3096, -1), (key3047, -1), (key3110, 2), (key3106, 2), (key3054, 2), (key3110, -1), (key3103, -1), (key3106, -1), (key3050, -1), (key3096, -1), (key3047, -1), (key3136, 2), (key3103, 2), (key3134, 2), (key3066, 2), (key3096, 2), (key3061, 2), (key3136, -1), (key3110, -1), (key3134, -1), (key3072, -1), (key3106, -1), (key3069, -1), (key3110, 2), (key3106, 2), (key3054, 2), (key3136, -1), (key3110, -1), (key3134, -1), (key3072, -1), (key3106, -1), (key3069, -1)]

def rawRow18195 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3050, 2), (key3050, 2), (key3103, 2), (key3061, -1), (key3069, -1), (key3061, -1), (key3136, -1), (key3069, -1), (key3136, -1), (key3047, 2), (key3072, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3110, 2), (key3050, -1), (key3066, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3103, -1), (key3069, 2), (key3069, 2), (key3136, 2), (key3054, -1), (key3072, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3110, -1)]

def rawRow18196 : Integer.Sparse Key := [(key2689, -1), (key2679, -1), (key3110, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3050, 2), (key3103, 2), (key3050, 2), (key3069, -1), (key3061, -1), (key3136, -1), (key3061, -1), (key3136, -1), (key3069, -1), (key3072, 2), (key3047, 2), (key3110, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3066, -1), (key3050, -1), (key3103, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3069, 2), (key3136, 2), (key3069, 2), (key3072, -1), (key3054, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3072, -1)]

def rawRow18197 : Integer.Sparse Key := [(key2955, -1), (key2955, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key3047, -1), (key3103, 2), (key3050, 2), (key3050, 2), (key3136, -1), (key3136, -1), (key3069, -1), (key3069, -1), (key3061, -1), (key3061, -1), (key3110, 2), (key3110, 2), (key3072, 2), (key3072, 2), (key3047, 2), (key3047, 2), (key3103, -1), (key3103, -1), (key3066, -1), (key3066, -1), (key3050, -1), (key3050, -1), (key3136, 2), (key3069, 2), (key3069, 2), (key3110, -1), (key3110, -1), (key3072, -1), (key3072, -1), (key3054, -1), (key3054, -1)]

def rawRow18198 : Integer.Sparse Key := [(key2682, -1), (key2689, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2679, 2), (key3047, 2), (key3096, 2), (key3066, -1), (key3072, -1), (key3066, -1), (key3134, -1), (key3072, -1), (key3134, -1), (key3050, 2), (key3069, 2), (key3050, 2), (key3106, 2), (key3069, 2), (key3106, 2), (key3047, -1), (key3061, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3096, -1), (key3072, 2), (key3072, 2), (key3134, 2), (key3054, -1), (key3069, -1), (key3054, -1), (key3106, -1), (key3069, -1), (key3106, -1)]

def rawRow18199 : Integer.Sparse Key := [(key2689, -1), (key2682, -1), (key2818, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2679, 2), (key3096, 2), (key3047, 2), (key3072, -1), (key3066, -1), (key3134, -1), (key3066, -1), (key3134, -1), (key3072, -1), (key3069, 2), (key3050, 2), (key3106, 2), (key3050, 2), (key3106, 2), (key3069, 2), (key3061, -1), (key3047, -1), (key3096, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3072, 2), (key3134, 2), (key3072, 2), (key3069, -1), (key3054, -1), (key3106, -1), (key3054, -1), (key3106, -1), (key3069, -1)]

def rawRow18200 : Integer.Sparse Key := [(key2818, -1), (key2818, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2813, 2), (key2679, 2), (key3047, 2), (key3134, -1), (key3134, -1), (key3072, -1), (key3072, -1), (key3066, -1), (key3066, -1), (key3106, 2), (key3106, 2), (key3069, 2), (key3069, 2), (key3050, 2), (key3050, 2), (key3096, -1), (key3096, -1), (key3061, -1), (key3061, -1), (key3047, -1), (key3047, -1), (key3134, 2), (key3072, 2), (key3072, 2), (key3106, -1), (key3106, -1), (key3069, -1), (key3069, -1), (key3054, -1), (key3054, -1)]

def rawRow18201 : Integer.Sparse Key := [(key2710, -1), (key2715, -1), (key2710, -1), (key2979, -1), (key2715, -1), (key2979, -1), (key2715, 2), (key2715, 2), (key2979, 2), (key2679, -1), (key2689, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3047, 2), (key3072, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3110, 2), (key3054, -1), (key3072, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3110, -1), (key3050, 2), (key3050, 2), (key3103, 2), (key3050, -1), (key3066, -1), (key3050, -1), (key3103, -1), (key3066, -1), (key3103, -1)]

def rawRow18202 : Integer.Sparse Key := [(key2715, -1), (key2710, -1), (key2979, -1), (key2710, -1), (key2979, -1), (key2715, -1), (key2715, 2), (key2979, 2), (key2715, 2), (key2689, -1), (key2679, -1), (key3110, -1), (key3047, -1), (key3110, -1), (key3054, -1), (key3072, 2), (key3047, 2), (key3110, 2), (key3047, 2), (key3110, 2), (key3072, 2), (key3072, -1), (key3054, -1), (key3110, -1), (key3054, -1), (key3110, -1), (key3072, -1), (key3050, 2), (key3103, 2), (key3050, 2), (key3066, -1), (key3050, -1), (key3103, -1), (key3050, -1), (key3103, -1), (key3066, -1)]

def rawRow18203 : Integer.Sparse Key := [(key2979, -1), (key2979, -1), (key2715, -1), (key2715, -1), (key2710, -1), (key2710, -1), (key2979, 2), (key2715, 2), (key2715, 2), (key2955, -1), (key2955, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key3047, -1), (key3110, 2), (key3110, 2), (key3072, 2), (key3072, 2), (key3047, 2), (key3047, 2), (key3110, -1), (key3110, -1), (key3072, -1), (key3072, -1), (key3054, -1), (key3054, -1), (key3103, 2), (key3050, 2), (key3050, 2), (key3103, -1), (key3103, -1), (key3066, -1), (key3066, -1), (key3050, -1), (key3050, -1)]

def rawRow18204 : Integer.Sparse Key := [(key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2710, 2), (key2710, 2), (key2710, 2), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2679, -1), (key2679, -1), (key2679, -1), (key3047, -1), (key3047, -1), (key3047, -1), (key3066, 2), (key3066, 2), (key3066, 2), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1), (key3050, -1)]

def rawRow18205 : Integer.Sparse Key := [(key2740, -1), (key2742, -1), (key2740, -1), (key2900, -1), (key2742, -1), (key2900, -1), (key2742, 2), (key2742, 2), (key2900, 2), (key2682, -1), (key2689, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2682, 2), (key2715, 2), (key2682, 2), (key2818, 2), (key2715, 2), (key2818, 2), (key2689, -1), (key2715, -1), (key2689, -1), (key2818, -1), (key2715, -1), (key2818, -1), (key2679, 2), (key3047, 2), (key3096, 2), (key3047, -1), (key3061, -1), (key3047, -1), (key3096, -1), (key3061, -1), (key3096, -1)]

def rawRow18206 : Integer.Sparse Key := [(key2742, -1), (key2740, -1), (key2900, -1), (key2740, -1), (key2900, -1), (key2742, -1), (key2742, 2), (key2900, 2), (key2742, 2), (key2689, -1), (key2682, -1), (key2818, -1), (key2682, -1), (key2818, -1), (key2689, -1), (key2715, 2), (key2682, 2), (key2818, 2), (key2682, 2), (key2818, 2), (key2715, 2), (key2715, -1), (key2689, -1), (key2818, -1), (key2689, -1), (key2818, -1), (key2715, -1), (key2679, 2), (key3096, 2), (key3047, 2), (key3061, -1), (key3047, -1), (key3096, -1), (key3047, -1), (key3096, -1), (key3061, -1)]

def rawRow18207 : Integer.Sparse Key := [(key2900, -1), (key2900, -1), (key2742, -1), (key2742, -1), (key2740, -1), (key2740, -1), (key2900, 2), (key2742, 2), (key2742, 2), (key2818, -1), (key2818, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2818, 2), (key2818, 2), (key2715, 2), (key2715, 2), (key2682, 2), (key2682, 2), (key2818, -1), (key2818, -1), (key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2813, 2), (key2679, 2), (key3047, 2), (key3096, -1), (key3096, -1), (key3061, -1), (key3061, -1), (key3047, -1), (key3047, -1)]

def rawRow18208 : Integer.Sparse Key := [(key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2742, -1), (key2740, 2), (key2740, 2), (key2740, 2), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2715, -1), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2689, 2), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2682, -1), (key2710, 2), (key2710, 2), (key2710, 2), (key2679, -1), (key2679, -1), (key2679, -1), (key3047, -1), (key3047, -1), (key3047, -1)]

def rawRow18209 : Integer.Sparse Key := [(key1500, -2), (key1503, -2), (key1507, -2), (key1507, 6), (key1500, -2), (key1503, -2), (key1507, -2), (key1500, 2), (key1503, 2), (key1732, 2), (key1874, 2), (key1736, 2), (key1875, 2), (key1507, -2), (key1736, -2), (key1875, -2), (key1507, 6), (key1507, -2), (key1736, -2), (key1875, -2)]

def rawRow18210 : Integer.Sparse Key := [(key1503, -2), (key1500, -2), (key1507, -2), (key1507, 6), (key1503, -2), (key1500, -2), (key1507, -2), (key1503, 2), (key1500, 2), (key1874, 2), (key1732, 2), (key1875, 2), (key1736, 2), (key1507, -2), (key1875, -2), (key1736, -2), (key1507, 6), (key1507, -2), (key1875, -2), (key1736, -2)]

def rawRow18211 : Integer.Sparse Key := [(key1500, -2), (key1507, -2), (key1503, -2), (key1507, 6), (key1500, -2), (key1507, -2), (key1503, -2), (key1732, 2), (key1736, 2), (key1500, 2), (key1875, 2), (key1503, 2), (key1874, 2), (key1736, -2), (key1507, -2), (key1875, -2), (key1507, 6), (key1736, -2), (key1507, -2), (key1875, -2)]

def rawRow18212 : Integer.Sparse Key := [(key1507, -2), (key1500, -2), (key1503, -2), (key1507, 6), (key1507, -2), (key1500, -2), (key1503, -2), (key1736, 2), (key1732, 2), (key1875, 2), (key1500, 2), (key1874, 2), (key1503, 2), (key1736, -2), (key1875, -2), (key1507, -2), (key1507, 6), (key1736, -2), (key1875, -2), (key1507, -2)]

def rawRow18213 : Integer.Sparse Key := [(key1503, -2), (key1507, -2), (key1500, -2), (key1507, 6), (key1503, -2), (key1507, -2), (key1500, -2), (key1874, 2), (key1875, 2), (key1503, 2), (key1736, 2), (key1500, 2), (key1732, 2), (key1875, -2), (key1507, -2), (key1736, -2), (key1507, 6), (key1875, -2), (key1507, -2), (key1736, -2)]

def rawRow18214 : Integer.Sparse Key := [(key1507, -2), (key1503, -2), (key1500, -2), (key1507, 6), (key1507, -2), (key1503, -2), (key1500, -2), (key1875, 2), (key1874, 2), (key1736, 2), (key1503, 2), (key1732, 2), (key1500, 2), (key1875, -2), (key1736, -2), (key1507, -2), (key1507, 6), (key1875, -2), (key1736, -2), (key1507, -2)]

def rawRow18215 : Integer.Sparse Key := [(key1500, -2), (key1507, -2), (key1507, -2), (key1503, 6), (key1732, -2), (key1736, -2), (key1736, -2), (key1500, 2), (key1507, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1875, 2), (key1503, -2), (key1503, -2), (key1874, -2), (key1736, 6), (key1507, -2), (key1507, -2), (key1875, -2)]

def rawRow18216 : Integer.Sparse Key := [(key1507, -2), (key1500, -2), (key1507, -2), (key1503, 6), (key1736, -2), (key1732, -2), (key1736, -2), (key1507, 2), (key1500, 2), (key1875, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1503, -2), (key1874, -2), (key1503, -2), (key1736, 6), (key1507, -2), (key1875, -2), (key1507, -2)]

def rawRow18217 : Integer.Sparse Key := [(key1507, -2), (key1507, -2), (key1500, -2), (key1503, 6), (key1736, -2), (key1736, -2), (key1732, -2), (key1875, 2), (key1875, 2), (key1507, 2), (key1507, 2), (key1500, 2), (key1500, 2), (key1874, -2), (key1503, -2), (key1503, -2), (key1736, 6), (key1875, -2), (key1507, -2), (key1507, -2)]

def rawRow18218 : Integer.Sparse Key := [(key1503, -2), (key1507, -2), (key1507, -2), (key1500, 6), (key1874, -2), (key1875, -2), (key1875, -2), (key1503, 2), (key1507, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1736, 2), (key1500, -2), (key1500, -2), (key1732, -2), (key1875, 6), (key1507, -2), (key1507, -2), (key1736, -2)]

def rawRow18219 : Integer.Sparse Key := [(key1507, -2), (key1503, -2), (key1507, -2), (key1500, 6), (key1875, -2), (key1874, -2), (key1875, -2), (key1507, 2), (key1503, 2), (key1736, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1500, -2), (key1732, -2), (key1500, -2), (key1875, 6), (key1507, -2), (key1736, -2), (key1507, -2)]

def rawRow18220 : Integer.Sparse Key := [(key1507, -2), (key1507, -2), (key1503, -2), (key1500, 6), (key1875, -2), (key1875, -2), (key1874, -2), (key1736, 2), (key1736, 2), (key1507, 2), (key1507, 2), (key1503, 2), (key1503, 2), (key1732, -2), (key1500, -2), (key1500, -2), (key1875, 6), (key1736, -2), (key1507, -2), (key1507, -2)]

def rawRow18221 : Integer.Sparse Key := [(key1732, -2), (key1736, -2), (key1736, -2), (key1736, 6), (key1500, -2), (key1507, -2), (key1507, -2), (key1500, 2), (key1507, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1875, 2), (key1507, -2), (key1507, -2), (key1875, -2), (key1503, 6), (key1503, -2), (key1503, -2), (key1874, -2)]

def rawRow18222 : Integer.Sparse Key := [(key1736, -2), (key1732, -2), (key1736, -2), (key1736, 6), (key1507, -2), (key1500, -2), (key1507, -2), (key1507, 2), (key1500, 2), (key1875, 2), (key1500, 2), (key1875, 2), (key1507, 2), (key1507, -2), (key1875, -2), (key1507, -2), (key1503, 6), (key1503, -2), (key1874, -2), (key1503, -2)]

def rawRow18223 : Integer.Sparse Key := [(key1736, -2), (key1736, -2), (key1732, -2), (key1736, 6), (key1507, -2), (key1507, -2), (key1500, -2), (key1875, 2), (key1875, 2), (key1507, 2), (key1507, 2), (key1500, 2), (key1500, 2), (key1875, -2), (key1507, -2), (key1507, -2), (key1503, 6), (key1874, -2), (key1503, -2), (key1503, -2)]

def rawRow18224 : Integer.Sparse Key := [(key1736, -2), (key1736, -2), (key1736, -2), (key1732, 6), (key1875, -2), (key1875, -2), (key1875, -2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1500, -2), (key1500, -2), (key1500, -2), (key1874, 6), (key1503, -2), (key1503, -2), (key1503, -2)]

def rawRow18225 : Integer.Sparse Key := [(key1874, -2), (key1875, -2), (key1875, -2), (key1875, 6), (key1503, -2), (key1507, -2), (key1507, -2), (key1503, 2), (key1507, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1736, 2), (key1507, -2), (key1507, -2), (key1736, -2), (key1500, 6), (key1500, -2), (key1500, -2), (key1732, -2)]

def rawRow18226 : Integer.Sparse Key := [(key1875, -2), (key1874, -2), (key1875, -2), (key1875, 6), (key1507, -2), (key1503, -2), (key1507, -2), (key1507, 2), (key1503, 2), (key1736, 2), (key1503, 2), (key1736, 2), (key1507, 2), (key1507, -2), (key1736, -2), (key1507, -2), (key1500, 6), (key1500, -2), (key1732, -2), (key1500, -2)]

def rawRow18227 : Integer.Sparse Key := [(key1875, -2), (key1875, -2), (key1874, -2), (key1875, 6), (key1507, -2), (key1507, -2), (key1503, -2), (key1736, 2), (key1736, 2), (key1507, 2), (key1507, 2), (key1503, 2), (key1503, 2), (key1736, -2), (key1507, -2), (key1507, -2), (key1500, 6), (key1732, -2), (key1500, -2), (key1500, -2)]

def rawRow18228 : Integer.Sparse Key := [(key1875, -2), (key1875, -2), (key1875, -2), (key1874, 6), (key1736, -2), (key1736, -2), (key1736, -2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1507, 2), (key1503, -2), (key1503, -2), (key1503, -2), (key1732, 6), (key1500, -2), (key1500, -2), (key1500, -2)]

def rawRow18229 : Integer.Sparse Key := [(key2421, 2), (key2428, 2), (key2429, 2), (key2428, -2), (key2429, -2), (key2442, -2), (key2421, 2), (key2428, 2), (key2429, 2), (key2428, -1), (key2429, -1), (key2496, -1), (key2550, -1), (key2508, -1), (key2556, -1), (key2428, -2), (key2429, -2), (key2442, -2), (key2428, -1), (key2429, -1), (key2496, -1), (key2550, -1), (key2508, -1), (key2556, -1), (key2442, 4), (key2508, 4), (key2556, 4)]

def rawRow18230 : Integer.Sparse Key := [(key2421, 2), (key2429, 2), (key2428, 2), (key2429, -2), (key2428, -2), (key2442, -2), (key2421, 2), (key2429, 2), (key2428, 2), (key2429, -1), (key2428, -1), (key2550, -1), (key2496, -1), (key2556, -1), (key2508, -1), (key2429, -2), (key2428, -2), (key2442, -2), (key2429, -1), (key2428, -1), (key2550, -1), (key2496, -1), (key2556, -1), (key2508, -1), (key2442, 4), (key2556, 4), (key2508, 4)]

def rawRow18231 : Integer.Sparse Key := [(key2428, 2), (key2421, 2), (key2429, 2), (key2428, -2), (key2442, -2), (key2429, -2), (key2428, 2), (key2421, 2), (key2429, 2), (key2496, -1), (key2508, -1), (key2428, -1), (key2556, -1), (key2429, -1), (key2550, -1), (key2428, -2), (key2442, -2), (key2429, -2), (key2496, -1), (key2508, -1), (key2428, -1), (key2556, -1), (key2429, -1), (key2550, -1), (key2508, 4), (key2442, 4), (key2556, 4)]

def rawRow18232 : Integer.Sparse Key := [(key2428, 2), (key2429, 2), (key2421, 2), (key2442, -2), (key2428, -2), (key2429, -2), (key2428, 2), (key2429, 2), (key2421, 2), (key2508, -1), (key2496, -1), (key2556, -1), (key2428, -1), (key2550, -1), (key2429, -1), (key2442, -2), (key2428, -2), (key2429, -2), (key2508, -1), (key2496, -1), (key2556, -1), (key2428, -1), (key2550, -1), (key2429, -1), (key2508, 4), (key2556, 4), (key2442, 4)]

def rawRow18233 : Integer.Sparse Key := [(key2429, 2), (key2421, 2), (key2428, 2), (key2429, -2), (key2442, -2), (key2428, -2), (key2429, 2), (key2421, 2), (key2428, 2), (key2550, -1), (key2556, -1), (key2429, -1), (key2508, -1), (key2428, -1), (key2496, -1), (key2429, -2), (key2442, -2), (key2428, -2), (key2550, -1), (key2556, -1), (key2429, -1), (key2508, -1), (key2428, -1), (key2496, -1), (key2556, 4), (key2442, 4), (key2508, 4)]

def rawRow18234 : Integer.Sparse Key := [(key2429, 2), (key2428, 2), (key2421, 2), (key2442, -2), (key2429, -2), (key2428, -2), (key2429, 2), (key2428, 2), (key2421, 2), (key2556, -1), (key2550, -1), (key2508, -1), (key2429, -1), (key2496, -1), (key2428, -1), (key2442, -2), (key2429, -2), (key2428, -2), (key2556, -1), (key2550, -1), (key2508, -1), (key2429, -1), (key2496, -1), (key2428, -1), (key2556, 4), (key2508, 4), (key2442, 4)]

def rawRow18235 : Integer.Sparse Key := [(key2428, 2), (key2428, 2), (key2442, 2), (key2421, -2), (key2429, -2), (key2429, -2), (key2496, 2), (key2496, 2), (key2508, 2), (key2421, -1), (key2429, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2550, -1), (key2496, -2), (key2508, -2), (key2508, -2), (key2428, -1), (key2442, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2556, -1), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow18236 : Integer.Sparse Key := [(key2428, 2), (key2442, 2), (key2428, 2), (key2429, -2), (key2421, -2), (key2429, -2), (key2496, 2), (key2508, 2), (key2496, 2), (key2429, -1), (key2421, -1), (key2550, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2508, -2), (key2496, -2), (key2508, -2), (key2442, -1), (key2428, -1), (key2556, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow18237 : Integer.Sparse Key := [(key2442, 2), (key2428, 2), (key2428, 2), (key2429, -2), (key2429, -2), (key2421, -2), (key2508, 2), (key2496, 2), (key2496, 2), (key2550, -1), (key2550, -1), (key2429, -1), (key2429, -1), (key2421, -1), (key2421, -1), (key2508, -2), (key2508, -2), (key2496, -2), (key2556, -1), (key2556, -1), (key2442, -1), (key2442, -1), (key2428, -1), (key2428, -1), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow18238 : Integer.Sparse Key := [(key2429, 2), (key2429, 2), (key2442, 2), (key2421, -2), (key2428, -2), (key2428, -2), (key2550, 2), (key2550, 2), (key2556, 2), (key2421, -1), (key2428, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2496, -1), (key2550, -2), (key2556, -2), (key2556, -2), (key2429, -1), (key2442, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2508, -1), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow18239 : Integer.Sparse Key := [(key2429, 2), (key2442, 2), (key2429, 2), (key2428, -2), (key2421, -2), (key2428, -2), (key2550, 2), (key2556, 2), (key2550, 2), (key2428, -1), (key2421, -1), (key2496, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2556, -2), (key2550, -2), (key2556, -2), (key2442, -1), (key2429, -1), (key2508, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18240 : Integer.Sparse Key := [(key2442, 2), (key2429, 2), (key2429, 2), (key2428, -2), (key2428, -2), (key2421, -2), (key2556, 2), (key2550, 2), (key2550, 2), (key2496, -1), (key2496, -1), (key2428, -1), (key2428, -1), (key2421, -1), (key2421, -1), (key2556, -2), (key2556, -2), (key2550, -2), (key2508, -1), (key2508, -1), (key2442, -1), (key2442, -1), (key2429, -1), (key2429, -1), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18241 : Integer.Sparse Key := [(key2496, 2), (key2496, 2), (key2508, 2), (key2496, -2), (key2508, -2), (key2508, -2), (key2428, 2), (key2428, 2), (key2442, 2), (key2428, -1), (key2442, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2556, -1), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -1), (key2429, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2550, -1), (key2429, 4), (key2429, 4), (key2550, 4)]

def rawRow18242 : Integer.Sparse Key := [(key2496, 2), (key2508, 2), (key2496, 2), (key2508, -2), (key2496, -2), (key2508, -2), (key2428, 2), (key2442, 2), (key2428, 2), (key2442, -1), (key2428, -1), (key2556, -1), (key2428, -1), (key2556, -1), (key2442, -1), (key2429, -2), (key2421, -2), (key2429, -2), (key2429, -1), (key2421, -1), (key2550, -1), (key2421, -1), (key2550, -1), (key2429, -1), (key2429, 4), (key2550, 4), (key2429, 4)]

def rawRow18243 : Integer.Sparse Key := [(key2508, 2), (key2496, 2), (key2496, 2), (key2508, -2), (key2508, -2), (key2496, -2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, -1), (key2556, -1), (key2442, -1), (key2442, -1), (key2428, -1), (key2428, -1), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -1), (key2550, -1), (key2429, -1), (key2429, -1), (key2421, -1), (key2421, -1), (key2550, 4), (key2429, 4), (key2429, 4)]

def rawRow18244 : Integer.Sparse Key := [(key2508, 2), (key2508, 2), (key2508, 2), (key2496, -2), (key2496, -2), (key2496, -2), (key2556, 2), (key2556, 2), (key2556, 2), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2550, -2), (key2550, -2), (key2550, -2), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18245 : Integer.Sparse Key := [(key2550, 2), (key2550, 2), (key2556, 2), (key2550, -2), (key2556, -2), (key2556, -2), (key2429, 2), (key2429, 2), (key2442, 2), (key2429, -1), (key2442, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2508, -1), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -1), (key2428, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2496, -1), (key2428, 4), (key2428, 4), (key2496, 4)]

def rawRow18246 : Integer.Sparse Key := [(key2550, 2), (key2556, 2), (key2550, 2), (key2556, -2), (key2550, -2), (key2556, -2), (key2429, 2), (key2442, 2), (key2429, 2), (key2442, -1), (key2429, -1), (key2508, -1), (key2429, -1), (key2508, -1), (key2442, -1), (key2428, -2), (key2421, -2), (key2428, -2), (key2428, -1), (key2421, -1), (key2496, -1), (key2421, -1), (key2496, -1), (key2428, -1), (key2428, 4), (key2496, 4), (key2428, 4)]

def rawRow18247 : Integer.Sparse Key := [(key2556, 2), (key2550, 2), (key2550, 2), (key2556, -2), (key2556, -2), (key2550, -2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, -1), (key2508, -1), (key2442, -1), (key2442, -1), (key2429, -1), (key2429, -1), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -1), (key2496, -1), (key2428, -1), (key2428, -1), (key2421, -1), (key2421, -1), (key2496, 4), (key2428, 4), (key2428, 4)]

def rawRow18248 : Integer.Sparse Key := [(key2556, 2), (key2556, 2), (key2556, 2), (key2550, -2), (key2550, -2), (key2550, -2), (key2508, 2), (key2508, 2), (key2508, 2), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2429, -1), (key2496, -2), (key2496, -2), (key2496, -2), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2428, -1), (key2421, 4), (key2421, 4), (key2421, 4)]

def rawRow18249 : Integer.Sparse Key := [(key2680, 2), (key2683, 2), (key2690, 2), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, 2), (key2683, 2), (key2690, 2), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, -1), (key2683, -1), (key2814, -1), (key2954, -1), (key2819, -1), (key2956, -1), (key2711, 2), (key2741, 2), (key2814, 2), (key2954, 2), (key2901, 2), (key2980, 2)]

def rawRow18250 : Integer.Sparse Key := [(key2683, 2), (key2680, 2), (key2690, 2), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, 2), (key2680, 2), (key2690, 2), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, -1), (key2680, -1), (key2954, -1), (key2814, -1), (key2956, -1), (key2819, -1), (key2741, 2), (key2711, 2), (key2954, 2), (key2814, 2), (key2980, 2), (key2901, 2)]

def rawRow18251 : Integer.Sparse Key := [(key2680, 2), (key2690, 2), (key2683, 2), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2680, 2), (key2690, 2), (key2683, 2), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2814, -1), (key2819, -1), (key2680, -1), (key2956, -1), (key2683, -1), (key2954, -1), (key2814, 2), (key2901, 2), (key2711, 2), (key2980, 2), (key2741, 2), (key2954, 2)]

def rawRow18252 : Integer.Sparse Key := [(key2690, 2), (key2680, 2), (key2683, 2), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2690, 2), (key2680, 2), (key2683, 2), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2819, -1), (key2814, -1), (key2956, -1), (key2680, -1), (key2954, -1), (key2683, -1), (key2901, 2), (key2814, 2), (key2980, 2), (key2711, 2), (key2954, 2), (key2741, 2)]

def rawRow18253 : Integer.Sparse Key := [(key2683, 2), (key2690, 2), (key2680, 2), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2683, 2), (key2690, 2), (key2680, 2), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2954, -1), (key2956, -1), (key2683, -1), (key2819, -1), (key2680, -1), (key2814, -1), (key2954, 2), (key2980, 2), (key2741, 2), (key2901, 2), (key2711, 2), (key2814, 2)]

def rawRow18254 : Integer.Sparse Key := [(key2690, 2), (key2683, 2), (key2680, 2), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2690, 2), (key2683, 2), (key2680, 2), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2956, -1), (key2954, -1), (key2819, -1), (key2683, -1), (key2814, -1), (key2680, -1), (key2980, 2), (key2954, 2), (key2901, 2), (key2741, 2), (key2814, 2), (key2711, 2)]

def rawRow18255 : Integer.Sparse Key := [(key2711, 2), (key2716, 2), (key2716, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2814, 2), (key2819, 2), (key2819, 2), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2)]

def rawRow18256 : Integer.Sparse Key := [(key2716, 2), (key2711, 2), (key2716, 2), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2819, 2), (key2814, 2), (key2819, 2), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2)]

def rawRow18257 : Integer.Sparse Key := [(key2716, 2), (key2716, 2), (key2711, 2), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2819, 2), (key2819, 2), (key2814, 2), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2)]

def rawRow18258 : Integer.Sparse Key := [(key2741, 2), (key2743, 2), (key2743, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2954, 2), (key2956, 2), (key2956, 2), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2)]

def rawRow18259 : Integer.Sparse Key := [(key2743, 2), (key2741, 2), (key2743, 2), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2956, 2), (key2954, 2), (key2956, 2), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2)]

def rawRow18260 : Integer.Sparse Key := [(key2743, 2), (key2743, 2), (key2741, 2), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2956, 2), (key2956, 2), (key2954, 2), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2)]

def rawRow18261 : Integer.Sparse Key := [(key2814, 2), (key2819, 2), (key2819, 2), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, -1), (key2716, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2980, -1), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2680, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2956, -1), (key2680, 2), (key2743, 2), (key2680, 2), (key2956, 2), (key2743, 2), (key2956, 2)]

def rawRow18262 : Integer.Sparse Key := [(key2819, 2), (key2814, 2), (key2819, 2), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, 2), (key2711, 2), (key2716, 2), (key2716, -1), (key2711, -1), (key2980, -1), (key2711, -1), (key2980, -1), (key2716, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2956, -1), (key2680, -1), (key2956, -1), (key2690, -1), (key2743, 2), (key2680, 2), (key2956, 2), (key2680, 2), (key2956, 2), (key2743, 2)]

def rawRow18263 : Integer.Sparse Key := [(key2819, 2), (key2819, 2), (key2814, 2), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, -1), (key2980, -1), (key2716, -1), (key2716, -1), (key2711, -1), (key2711, -1), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, -1), (key2956, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 2), (key2956, 2), (key2743, 2), (key2743, 2), (key2680, 2), (key2680, 2)]

def rawRow18264 : Integer.Sparse Key := [(key2901, 2), (key2901, 2), (key2901, 2), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2980, 2), (key2980, 2), (key2980, 2), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2)]

def rawRow18265 : Integer.Sparse Key := [(key2954, 2), (key2956, 2), (key2956, 2), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, -1), (key2743, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2901, -1), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2683, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2819, -1), (key2683, 2), (key2716, 2), (key2683, 2), (key2819, 2), (key2716, 2), (key2819, 2)]

def rawRow18266 : Integer.Sparse Key := [(key2956, 2), (key2954, 2), (key2956, 2), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, 2), (key2741, 2), (key2743, 2), (key2743, -1), (key2741, -1), (key2901, -1), (key2741, -1), (key2901, -1), (key2743, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2819, -1), (key2683, -1), (key2819, -1), (key2690, -1), (key2716, 2), (key2683, 2), (key2819, 2), (key2683, 2), (key2819, 2), (key2716, 2)]

def rawRow18267 : Integer.Sparse Key := [(key2956, 2), (key2956, 2), (key2954, 2), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, -1), (key2901, -1), (key2743, -1), (key2743, -1), (key2741, -1), (key2741, -1), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, -1), (key2819, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 2), (key2819, 2), (key2716, 2), (key2716, 2), (key2683, 2), (key2683, 2)]

def rawRow18268 : Integer.Sparse Key := [(key2980, 2), (key2980, 2), (key2980, 2), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2901, 2), (key2901, 2), (key2901, 2), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2743, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2716, -1), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2), (key2690, 2)]

def rawRow18269 : Integer.Sparse Key := [(key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2690, 2), (key2716, 2), (key2743, 2), (key2680, 1), (key2683, 1), (key2814, 1), (key2954, 1), (key2819, 1), (key2956, 1), (key2690, -2), (key2819, -2), (key2956, -2), (key2680, -1), (key2683, -1), (key2711, -1), (key2741, -1), (key2716, -1), (key2743, -1), (key2680, 1), (key2683, 1), (key2814, 1), (key2954, 1), (key2819, 1), (key2956, 1), (key2690, 2), (key2716, 2), (key2743, 2), (key2690, -2), (key2819, -2), (key2956, -2)]

def rawRow18270 : Integer.Sparse Key := [(key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2690, 2), (key2743, 2), (key2716, 2), (key2683, 1), (key2680, 1), (key2954, 1), (key2814, 1), (key2956, 1), (key2819, 1), (key2690, -2), (key2956, -2), (key2819, -2), (key2683, -1), (key2680, -1), (key2741, -1), (key2711, -1), (key2743, -1), (key2716, -1), (key2683, 1), (key2680, 1), (key2954, 1), (key2814, 1), (key2956, 1), (key2819, 1), (key2690, 2), (key2743, 2), (key2716, 2), (key2690, -2), (key2956, -2), (key2819, -2)]

def rawRow18271 : Integer.Sparse Key := [(key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2716, 2), (key2690, 2), (key2743, 2), (key2814, 1), (key2819, 1), (key2680, 1), (key2956, 1), (key2683, 1), (key2954, 1), (key2819, -2), (key2690, -2), (key2956, -2), (key2711, -1), (key2716, -1), (key2680, -1), (key2743, -1), (key2683, -1), (key2741, -1), (key2814, 1), (key2819, 1), (key2680, 1), (key2956, 1), (key2683, 1), (key2954, 1), (key2716, 2), (key2690, 2), (key2743, 2), (key2819, -2), (key2690, -2), (key2956, -2)]

def rawRow18272 : Integer.Sparse Key := [(key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2716, 2), (key2743, 2), (key2690, 2), (key2819, 1), (key2814, 1), (key2956, 1), (key2680, 1), (key2954, 1), (key2683, 1), (key2819, -2), (key2956, -2), (key2690, -2), (key2716, -1), (key2711, -1), (key2743, -1), (key2680, -1), (key2741, -1), (key2683, -1), (key2819, 1), (key2814, 1), (key2956, 1), (key2680, 1), (key2954, 1), (key2683, 1), (key2716, 2), (key2743, 2), (key2690, 2), (key2819, -2), (key2956, -2), (key2690, -2)]

def rawRow18273 : Integer.Sparse Key := [(key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2743, 2), (key2690, 2), (key2716, 2), (key2954, 1), (key2956, 1), (key2683, 1), (key2819, 1), (key2680, 1), (key2814, 1), (key2956, -2), (key2690, -2), (key2819, -2), (key2741, -1), (key2743, -1), (key2683, -1), (key2716, -1), (key2680, -1), (key2711, -1), (key2954, 1), (key2956, 1), (key2683, 1), (key2819, 1), (key2680, 1), (key2814, 1), (key2743, 2), (key2690, 2), (key2716, 2), (key2956, -2), (key2690, -2), (key2819, -2)]

def rawRow18274 : Integer.Sparse Key := [(key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2743, 2), (key2716, 2), (key2690, 2), (key2956, 1), (key2954, 1), (key2819, 1), (key2683, 1), (key2814, 1), (key2680, 1), (key2956, -2), (key2819, -2), (key2690, -2), (key2743, -1), (key2741, -1), (key2716, -1), (key2683, -1), (key2711, -1), (key2680, -1), (key2956, 1), (key2954, 1), (key2819, 1), (key2683, 1), (key2814, 1), (key2680, 1), (key2743, 2), (key2716, 2), (key2690, 2), (key2956, -2), (key2819, -2), (key2690, -2)]

def rawRow18275 : Integer.Sparse Key := [(key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2683, 2), (key2683, 2), (key2741, 2), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2683, -2), (key2683, -2), (key2954, -2), (key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2711, 1), (key2716, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2980, 1), (key2819, 2), (key2819, 2), (key2901, 2), (key2716, -2), (key2716, -2), (key2980, -2)]

def rawRow18276 : Integer.Sparse Key := [(key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2683, 2), (key2741, 2), (key2683, 2), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2683, -2), (key2954, -2), (key2683, -2), (key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2716, 1), (key2711, 1), (key2980, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2819, 2), (key2901, 2), (key2819, 2), (key2716, -2), (key2980, -2), (key2716, -2)]

def rawRow18277 : Integer.Sparse Key := [(key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2741, 2), (key2683, 2), (key2683, 2), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2954, -2), (key2683, -2), (key2683, -2), (key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2980, 1), (key2980, 1), (key2716, 1), (key2716, 1), (key2711, 1), (key2711, 1), (key2901, 2), (key2819, 2), (key2819, 2), (key2980, -2), (key2716, -2), (key2716, -2)]

def rawRow18278 : Integer.Sparse Key := [(key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2680, 2), (key2680, 2), (key2711, 2), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2680, -2), (key2680, -2), (key2814, -2), (key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2741, 1), (key2743, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2901, 1), (key2956, 2), (key2956, 2), (key2980, 2), (key2743, -2), (key2743, -2), (key2901, -2)]

def rawRow18279 : Integer.Sparse Key := [(key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2680, 2), (key2711, 2), (key2680, 2), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2680, -2), (key2814, -2), (key2680, -2), (key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2743, 1), (key2741, 1), (key2901, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2956, 2), (key2980, 2), (key2956, 2), (key2743, -2), (key2901, -2), (key2743, -2)]

def rawRow18280 : Integer.Sparse Key := [(key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2711, 2), (key2680, 2), (key2680, 2), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2814, -2), (key2680, -2), (key2680, -2), (key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2901, 1), (key2901, 1), (key2743, 1), (key2743, 1), (key2741, 1), (key2741, 1), (key2980, 2), (key2956, 2), (key2956, 2), (key2901, -2), (key2743, -2), (key2743, -2)]

def rawRow18281 : Integer.Sparse Key := [(key2814, -1), (key2819, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2901, -1), (key2819, 2), (key2819, 2), (key2901, 2), (key2711, 1), (key2716, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2980, 1), (key2716, -2), (key2716, -2), (key2980, -2), (key2680, -1), (key2690, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2743, -1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2683, 2), (key2683, 2), (key2741, 2), (key2683, -2), (key2683, -2), (key2954, -2)]

def rawRow18282 : Integer.Sparse Key := [(key2819, -1), (key2814, -1), (key2901, -1), (key2814, -1), (key2901, -1), (key2819, -1), (key2819, 2), (key2901, 2), (key2819, 2), (key2716, 1), (key2711, 1), (key2980, 1), (key2711, 1), (key2980, 1), (key2716, 1), (key2716, -2), (key2980, -2), (key2716, -2), (key2690, -1), (key2680, -1), (key2743, -1), (key2680, -1), (key2743, -1), (key2690, -1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2683, 2), (key2741, 2), (key2683, 2), (key2683, -2), (key2954, -2), (key2683, -2)]

def rawRow18283 : Integer.Sparse Key := [(key2901, -1), (key2901, -1), (key2819, -1), (key2819, -1), (key2814, -1), (key2814, -1), (key2901, 2), (key2819, 2), (key2819, 2), (key2980, 1), (key2980, 1), (key2716, 1), (key2716, 1), (key2711, 1), (key2711, 1), (key2980, -2), (key2716, -2), (key2716, -2), (key2743, -1), (key2743, -1), (key2690, -1), (key2690, -1), (key2680, -1), (key2680, -1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2741, 2), (key2683, 2), (key2683, 2), (key2954, -2), (key2683, -2), (key2683, -2)]

def rawRow18284 : Integer.Sparse Key := [(key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2814, 2), (key2814, 2), (key2814, 2), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2711, -2), (key2711, -2), (key2711, -2), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2954, 2), (key2954, 2), (key2954, 2), (key2741, -2), (key2741, -2), (key2741, -2)]

def rawRow18285 : Integer.Sparse Key := [(key2954, -1), (key2956, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2980, -1), (key2956, 2), (key2956, 2), (key2980, 2), (key2741, 1), (key2743, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2901, 1), (key2743, -2), (key2743, -2), (key2901, -2), (key2683, -1), (key2690, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2716, -1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2680, 2), (key2680, 2), (key2711, 2), (key2680, -2), (key2680, -2), (key2814, -2)]

def rawRow18286 : Integer.Sparse Key := [(key2956, -1), (key2954, -1), (key2980, -1), (key2954, -1), (key2980, -1), (key2956, -1), (key2956, 2), (key2980, 2), (key2956, 2), (key2743, 1), (key2741, 1), (key2901, 1), (key2741, 1), (key2901, 1), (key2743, 1), (key2743, -2), (key2901, -2), (key2743, -2), (key2690, -1), (key2683, -1), (key2716, -1), (key2683, -1), (key2716, -1), (key2690, -1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2680, 2), (key2711, 2), (key2680, 2), (key2680, -2), (key2814, -2), (key2680, -2)]

def rawRow18287 : Integer.Sparse Key := [(key2980, -1), (key2980, -1), (key2956, -1), (key2956, -1), (key2954, -1), (key2954, -1), (key2980, 2), (key2956, 2), (key2956, 2), (key2901, 1), (key2901, 1), (key2743, 1), (key2743, 1), (key2741, 1), (key2741, 1), (key2901, -2), (key2743, -2), (key2743, -2), (key2716, -1), (key2716, -1), (key2690, -1), (key2690, -1), (key2683, -1), (key2683, -1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2711, 2), (key2680, 2), (key2680, 2), (key2814, -2), (key2680, -2), (key2680, -2)]

def rawRow18288 : Integer.Sparse Key := [(key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2956, -1), (key2954, 2), (key2954, 2), (key2954, 2), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2741, -2), (key2741, -2), (key2741, -2), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2819, -1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2814, 2), (key2814, 2), (key2814, 2), (key2711, -2), (key2711, -2), (key2711, -2)]

def rawRow18289 : Integer.Sparse Key := [(key2679, -1), (key2682, -1), (key2710, -1), (key2740, -1), (key2715, -1), (key2742, -1), (key2689, 2), (key2715, 2), (key2742, 2), (key3047, 1), (key3050, 1), (key3096, 1), (key3103, 1), (key3106, 1), (key3110, 1), (key3054, -2), (key3106, -2), (key3110, -2), (key3047, -1), (key3050, -1), (key3061, -1), (key3066, -1), (key3069, -1), (key3072, -1), (key3047, 1), (key3050, 1), (key3096, 1), (key3103, 1), (key3106, 1), (key3110, 1), (key3054, 2), (key3069, 2), (key3072, 2), (key3054, -2), (key3106, -2), (key3110, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18456 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key0, 24), (key83, 24), (key83, 24)]

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

def rawRow1785 : Integer.Sparse Key := [(key1677, -6), (key1525, 2), (key1603, 2), (key1603, 2), (key1914, 6), (key1250, -2), (key1603, -2), (key1603, -2), (key1892, -2), (key1914, -2), (key1914, -2), (key1269, 2), (key1677, 2), (key1677, 2)]

def rawRow1786 : Integer.Sparse Key := [(key1677, -6), (key1603, 2), (key1525, 2), (key1603, 2), (key1914, 6), (key1603, -2), (key1250, -2), (key1603, -2), (key1914, -2), (key1892, -2), (key1914, -2), (key1677, 2), (key1269, 2), (key1677, 2)]

def rawRow1787 : Integer.Sparse Key := [(key1677, -6), (key1603, 2), (key1603, 2), (key1525, 2), (key1914, 6), (key1603, -2), (key1603, -2), (key1250, -2), (key1914, -2), (key1914, -2), (key1892, -2), (key1677, 2), (key1677, 2), (key1269, 2)]

def rawRow1789 : Integer.Sparse Key := [(key1914, -6), (key1892, 2), (key1914, 2), (key1914, 2), (key1677, 6), (key1269, -2), (key1677, -2), (key1677, -2), (key1525, -2), (key1603, -2), (key1603, -2), (key1250, 2), (key1603, 2), (key1603, 2)]

def rawRow1790 : Integer.Sparse Key := [(key1914, -6), (key1914, 2), (key1892, 2), (key1914, 2), (key1677, 6), (key1677, -2), (key1269, -2), (key1677, -2), (key1603, -2), (key1525, -2), (key1603, -2), (key1603, 2), (key1250, 2), (key1603, 2)]

def rawRow1791 : Integer.Sparse Key := [(key1914, -6), (key1914, 2), (key1914, 2), (key1892, 2), (key1677, 6), (key1677, -2), (key1677, -2), (key1269, -2), (key1603, -2), (key1603, -2), (key1525, -2), (key1603, 2), (key1603, 2), (key1250, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1792 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2370, 1), (key2376, 1), (key2370, 1), (key2388, 1), (key2376, 1), (key2388, 1), (key2398, 2), (key2404, 2), (key2404, 2), (key2398, -1), (key2404, -1), (key2398, -1), (key2435, -1), (key2404, -1), (key2435, -1), (key2464, -1), (key2470, -1), (key2464, -1), (key2478, -1), (key2470, -1), (key2478, -1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1)]

def rawRow1793 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2376, 1), (key2370, 1), (key2388, 1), (key2370, 1), (key2388, 1), (key2376, 1), (key2404, 2), (key2398, 2), (key2404, 2), (key2404, -1), (key2398, -1), (key2435, -1), (key2398, -1), (key2435, -1), (key2404, -1), (key2470, -1), (key2464, -1), (key2478, -1), (key2464, -1), (key2478, -1), (key2470, -1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1)]

def rawRow1794 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, 1), (key2388, 1), (key2376, 1), (key2376, 1), (key2370, 1), (key2370, 1), (key2404, 2), (key2404, 2), (key2398, 2), (key2435, -1), (key2435, -1), (key2404, -1), (key2404, -1), (key2398, -1), (key2398, -1), (key2478, -1), (key2478, -1), (key2470, -1), (key2470, -1), (key2464, -1), (key2464, -1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1)]

def rawRow1796 : Integer.Sparse Key := [(key2762, -2), (key2768, -2), (key2768, -2), (key2839, 1), (key2845, 1), (key2839, 1), (key2916, 1), (key2845, 1), (key2916, 1), (key2583, 2), (key2589, 2), (key2589, 2), (key2839, -1), (key2845, -1), (key2839, -1), (key3019, -1), (key2845, -1), (key3019, -1), (key2370, -1), (key2376, -1), (key2370, -1), (key2388, -1), (key2376, -1), (key2388, -1), (key2398, 1), (key2404, 1), (key2398, 1), (key2435, 1), (key2404, 1), (key2435, 1)]

def rawRow1797 : Integer.Sparse Key := [(key2768, -2), (key2762, -2), (key2768, -2), (key2845, 1), (key2839, 1), (key2916, 1), (key2839, 1), (key2916, 1), (key2845, 1), (key2589, 2), (key2583, 2), (key2589, 2), (key2845, -1), (key2839, -1), (key3019, -1), (key2839, -1), (key3019, -1), (key2845, -1), (key2376, -1), (key2370, -1), (key2388, -1), (key2370, -1), (key2388, -1), (key2376, -1), (key2404, 1), (key2398, 1), (key2435, 1), (key2398, 1), (key2435, 1), (key2404, 1)]

def rawRow1798 : Integer.Sparse Key := [(key2768, -2), (key2768, -2), (key2762, -2), (key2916, 1), (key2916, 1), (key2845, 1), (key2845, 1), (key2839, 1), (key2839, 1), (key2589, 2), (key2589, 2), (key2583, 2), (key3019, -1), (key3019, -1), (key2845, -1), (key2845, -1), (key2839, -1), (key2839, -1), (key2388, -1), (key2388, -1), (key2376, -1), (key2376, -1), (key2370, -1), (key2370, -1), (key2435, 1), (key2435, 1), (key2404, 1), (key2404, 1), (key2398, 1), (key2398, 1)]

def rawRow1799 : Integer.Sparse Key := [(key2916, -2), (key2916, -2), (key2925, -2), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key3019, 2), (key3019, 2), (key3028, 2), (key2589, -1), (key2589, -1), (key2845, -1), (key2845, -1), (key2876, -1), (key2876, -1), (key3005, -1), (key3005, -1), (key3019, -1), (key3019, -1), (key3028, -1), (key3028, -1), (key2604, 1), (key2604, 1), (key2916, 1), (key2916, 1), (key2925, 1), (key2925, 1)]

def rawRow1800 : Integer.Sparse Key := [(key2916, -2), (key2925, -2), (key2916, -2), (key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key3019, 2), (key3028, 2), (key3019, 2), (key2845, -1), (key2876, -1), (key2589, -1), (key2876, -1), (key2589, -1), (key2845, -1), (key3019, -1), (key3028, -1), (key3005, -1), (key3028, -1), (key3005, -1), (key3019, -1), (key2916, 1), (key2925, 1), (key2604, 1), (key2925, 1), (key2604, 1), (key2916, 1)]

def rawRow1801 : Integer.Sparse Key := [(key2925, -2), (key2916, -2), (key2916, -2), (key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key3028, 2), (key3019, 2), (key3019, 2), (key2876, -1), (key2845, -1), (key2876, -1), (key2589, -1), (key2845, -1), (key2589, -1), (key3028, -1), (key3019, -1), (key3028, -1), (key3005, -1), (key3019, -1), (key3005, -1), (key2925, 1), (key2916, 1), (key2925, 1), (key2604, 1), (key2916, 1), (key2604, 1)]

def rawRow1803 : Integer.Sparse Key := [(key3019, -2), (key3019, -2), (key3028, -2), (key3005, 1), (key3005, 1), (key3019, 1), (key3019, 1), (key3028, 1), (key3028, 1), (key2916, 2), (key2916, 2), (key2925, 2), (key2604, -1), (key2604, -1), (key2916, -1), (key2916, -1), (key2925, -1), (key2925, -1), (key2768, -1), (key2768, -1), (key2845, -1), (key2845, -1), (key2876, -1), (key2876, -1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1)]

def rawRow1804 : Integer.Sparse Key := [(key3019, -2), (key3028, -2), (key3019, -2), (key3019, 1), (key3028, 1), (key3005, 1), (key3028, 1), (key3005, 1), (key3019, 1), (key2916, 2), (key2925, 2), (key2916, 2), (key2916, -1), (key2925, -1), (key2604, -1), (key2925, -1), (key2604, -1), (key2916, -1), (key2845, -1), (key2876, -1), (key2768, -1), (key2876, -1), (key2768, -1), (key2845, -1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1)]

def rawRow1805 : Integer.Sparse Key := [(key3028, -2), (key3019, -2), (key3019, -2), (key3028, 1), (key3019, 1), (key3028, 1), (key3005, 1), (key3019, 1), (key3005, 1), (key2925, 2), (key2916, 2), (key2916, 2), (key2925, -1), (key2916, -1), (key2925, -1), (key2604, -1), (key2916, -1), (key2604, -1), (key2876, -1), (key2845, -1), (key2876, -1), (key2768, -1), (key2845, -1), (key2768, -1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1)]

def rawRow1806 : Integer.Sparse Key := [(key971, -2), (key979, -2), (key979, -2), (key979, 6), (key1085, 2), (key1093, 2), (key1093, 2), (key1093, -2), (key1093, -2), (key1228, -2), (key1164, -6), (key1164, 2), (key1164, 2), (key1245, 2)]

def rawRow1807 : Integer.Sparse Key := [(key979, -2), (key971, -2), (key979, -2), (key979, 6), (key1093, 2), (key1085, 2), (key1093, 2), (key1093, -2), (key1228, -2), (key1093, -2), (key1164, -6), (key1164, 2), (key1245, 2), (key1164, 2)]

def rawRow1808 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key971, -2), (key979, 6), (key1093, 2), (key1093, 2), (key1085, 2), (key1228, -2), (key1093, -2), (key1093, -2), (key1164, -6), (key1245, 2), (key1164, 2), (key1164, 2)]

def rawRow1810 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key971, 2), (key979, 2), (key979, 2), (key1164, -2), (key1164, -2), (key1245, -2), (key979, -6), (key1093, 2), (key1093, 2), (key1228, 2)]

def rawRow1811 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1093, -2), (key1164, 6), (key979, 2), (key971, 2), (key979, 2), (key1164, -2), (key1245, -2), (key1164, -2), (key979, -6), (key1093, 2), (key1228, 2), (key1093, 2)]

def rawRow1812 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1085, -2), (key1164, 6), (key979, 2), (key979, 2), (key971, 2), (key1245, -2), (key1164, -2), (key1164, -2), (key979, -6), (key1228, 2), (key1093, 2), (key1093, 2)]

def rawRow1813 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1164, -2), (key1085, 6), (key1228, 2), (key1228, 2), (key1245, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1228, -6), (key979, 2), (key1093, 2), (key1093, 2)]

def rawRow1814 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1093, -2), (key1085, 6), (key1228, 2), (key1245, 2), (key1228, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1228, -6), (key1093, 2), (key979, 2), (key1093, 2)]

def rawRow1815 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key1245, 2), (key1228, 2), (key1228, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1228, -6), (key1093, 2), (key1093, 2), (key979, 2)]

def rawRow1817 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1245, -2), (key1228, 6), (key1093, 2), (key1093, 2), (key1164, 2), (key979, -2), (key1093, -2), (key1093, -2), (key1085, -6), (key971, 2), (key1085, 2), (key1085, 2)]

def rawRow1818 : Integer.Sparse Key := [(key1228, -2), (key1245, -2), (key1228, -2), (key1228, 6), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, -2), (key979, -2), (key1093, -2), (key1085, -6), (key1085, 2), (key971, 2), (key1085, 2)]

def rawRow1819 : Integer.Sparse Key := [(key1245, -2), (key1228, -2), (key1228, -2), (key1228, 6), (key1164, 2), (key1093, 2), (key1093, 2), (key1093, -2), (key1093, -2), (key979, -2), (key1085, -6), (key1085, 2), (key1085, 2), (key971, 2)]

def rawRow1820 : Integer.Sparse Key := [(key2372, -6), (key2372, 2), (key2372, 2), (key2385, 2), (key2400, 6), (key2400, -2), (key2400, -2), (key2432, -2), (key2466, -2), (key2466, -2), (key2475, -2), (key2466, 2), (key2466, 2), (key2498, 2)]

def rawRow1821 : Integer.Sparse Key := [(key2372, -6), (key2372, 2), (key2385, 2), (key2372, 2), (key2400, 6), (key2400, -2), (key2432, -2), (key2400, -2), (key2466, -2), (key2475, -2), (key2466, -2), (key2466, 2), (key2498, 2), (key2466, 2)]

def rawRow1822 : Integer.Sparse Key := [(key2372, -6), (key2385, 2), (key2372, 2), (key2372, 2), (key2400, 6), (key2432, -2), (key2400, -2), (key2400, -2), (key2475, -2), (key2466, -2), (key2466, -2), (key2498, 2), (key2466, 2), (key2466, 2)]

def rawRow1824 : Integer.Sparse Key := [(key2400, -6), (key2466, 2), (key2466, 2), (key2475, 2), (key2372, 6), (key2466, -2), (key2466, -2), (key2498, -2), (key2372, -2), (key2372, -2), (key2385, -2), (key2400, 2), (key2400, 2), (key2432, 2)]

def rawRow1825 : Integer.Sparse Key := [(key2400, -6), (key2466, 2), (key2475, 2), (key2466, 2), (key2372, 6), (key2466, -2), (key2498, -2), (key2466, -2), (key2372, -2), (key2385, -2), (key2372, -2), (key2400, 2), (key2432, 2), (key2400, 2)]

def rawRow1826 : Integer.Sparse Key := [(key2400, -6), (key2475, 2), (key2466, 2), (key2466, 2), (key2372, 6), (key2498, -2), (key2466, -2), (key2466, -2), (key2385, -2), (key2372, -2), (key2372, -2), (key2432, 2), (key2400, 2), (key2400, 2)]

def rawRow1827 : Integer.Sparse Key := [(key2475, -6), (key2400, 2), (key2466, 2), (key2466, 2), (key2498, 6), (key2372, -2), (key2466, -2), (key2466, -2), (key2432, -2), (key2498, -2), (key2498, -2), (key2385, 2), (key2475, 2), (key2475, 2)]

def rawRow1828 : Integer.Sparse Key := [(key2475, -6), (key2466, 2), (key2400, 2), (key2466, 2), (key2498, 6), (key2466, -2), (key2372, -2), (key2466, -2), (key2498, -2), (key2432, -2), (key2498, -2), (key2475, 2), (key2385, 2), (key2475, 2)]

end MUB6.Certificate.GramRows

end OAI
end


