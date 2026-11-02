-- Prove2me | Definitions.Def_OAIQ106D164
-- name    : OAIQ106D164
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:31:48.971391+00:00
-- url     : https://prove2.me/theorems/29fdcc97-f32d-448e-93f0-4016109d3698
-- title:
--   Definitions bundle OAIQ106D164 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 549 declarations of OpenAI's Lean: 549 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow17330`, `OAI.MUB6.Certificate.GramRows.rawRow17331`, `OAI.MUB6.Certificate.GramRows.rawRow17332`, `OAI.MUB6.Certificate.GramRows.rawRow17333`, `OAI.MUB6.Certificate.GramRows.rawRow17334`, `OAI.MUB6.Certificate.GramRows.rawRow17335`, `OAI.MUB6.Certificate.GramRows.rawRow17336`, `OAI.MUB6.Certificate.GramRows.rawRow17337`, `OAI.MUB6.Certificate.GramRows.rawRow17338`, `OAI.MUB6.Certificate.GramRows.rawRow17339`, `OAI.MUB6.Certificate.GramRows.rawRow1734`, `OAI.MUB6.Certificate.GramRows.rawRow17340`, `OAI.MUB6.Certificate.GramRows.rawRow17341`, `OAI.MUB6.Certificate.GramRows.rawRow17342`, `OAI.MUB6.Certificate.GramRows.rawRow17343`, `OAI.MUB6.Certificate.GramRows.rawRow17344`, `OAI.MUB6.Certificate.GramRows.rawRow17345`, `OAI.MUB6.Certificate.GramRows.rawRow17346`, `OAI.MUB6.Certificate.GramRows.rawRow17347`, `OAI.MUB6.Certificate.GramRows.rawRow17348`, `OAI.MUB6.Certificate.GramRows.rawRow17349`, `OAI.MUB6.Certificate.GramRows.rawRow1735`, `OAI.MUB6.Certificate.GramRows.rawRow17350`, `OAI.MUB6.Certificate.GramRows.rawRow17351`, `OAI.MUB6.Certificate.GramRows.rawRow17352`, `OAI.MUB6.Certificate.GramRows.rawRow17353`, `OAI.MUB6.Certificate.GramRows.rawRow17354`, `OAI.MUB6.Certificate.GramRows.rawRow17355`, `OAI.MUB6.Certificate.GramRows.rawRow17356`, `OAI.MUB6.Certificate.GramRows.rawRow17357`, `OAI.MUB6.Certificate.GramRows.rawRow17358`, `OAI.MUB6.Certificate.GramRows.rawRow17359`, `OAI.MUB6.Certificate.GramRows.rawRow1736`, `OAI.MUB6.Certificate.GramRows.rawRow17360`, `OAI.MUB6.Certificate.GramRows.rawRow17361`, `OAI.MUB6.Certificate.GramRows.rawRow17362`, `OAI.MUB6.Certificate.GramRows.rawRow17363`, `OAI.MUB6.Certificate.GramRows.rawRow17364`, `OAI.MUB6.Certificate.GramRows.rawRow17365`, `OAI.MUB6.Certificate.GramRows.rawRow17366` and 509 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block159`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block159.lean), [`MutuallyUnbiased_GramRows_Block160`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block160.lean), [`MutuallyUnbiased_GramRows_Block161`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block161.lean), [`MutuallyUnbiased_GramRows_Block162`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block162.lean), [`MutuallyUnbiased_GramRows_Block163`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block163.lean), [`MutuallyUnbiased_GramRows_Block164`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block164.lean), [`MutuallyUnbiased_GramRows_Block37`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block37.lean), [`MutuallyUnbiased_TaoCertificate_Merge2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge2.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092`, `OAIQ106D094` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval18_18`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval20_12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow13`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow9` and `OAI.MUB6.TaoCertificate.combined393_zero`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17330 : Integer.Sparse Key := [(key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2134, 2), (key2134, 2), (key2134, 2), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2047, -2), (key2047, -2), (key2047, -2), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2127, 2), (key2127, 2), (key2127, 2), (key2042, -2), (key2042, -2), (key2042, -2)]

def rawRow17331 : Integer.Sparse Key := [(key2014, -1), (key2018, -1), (key2043, -1), (key2046, -1), (key2051, -1), (key2052, -1), (key2023, 2), (key2051, 2), (key2052, 2), (key2014, 1), (key2018, 1), (key2128, 1), (key2133, 1), (key2138, 1), (key2141, 1), (key2023, -2), (key2138, -2), (key2141, -2), (key2014, -1), (key2018, -1), (key2043, -1), (key2046, -1), (key2051, -1), (key2052, -1), (key2014, 1), (key2018, 1), (key2128, 1), (key2133, 1), (key2138, 1), (key2141, 1), (key2023, 2), (key2051, 2), (key2052, 2), (key2023, -2), (key2138, -2), (key2141, -2)]

def rawRow17332 : Integer.Sparse Key := [(key2018, -1), (key2014, -1), (key2046, -1), (key2043, -1), (key2052, -1), (key2051, -1), (key2023, 2), (key2052, 2), (key2051, 2), (key2018, 1), (key2014, 1), (key2133, 1), (key2128, 1), (key2141, 1), (key2138, 1), (key2023, -2), (key2141, -2), (key2138, -2), (key2018, -1), (key2014, -1), (key2046, -1), (key2043, -1), (key2052, -1), (key2051, -1), (key2018, 1), (key2014, 1), (key2133, 1), (key2128, 1), (key2141, 1), (key2138, 1), (key2023, 2), (key2052, 2), (key2051, 2), (key2023, -2), (key2141, -2), (key2138, -2)]

def rawRow17333 : Integer.Sparse Key := [(key2043, -1), (key2051, -1), (key2014, -1), (key2052, -1), (key2018, -1), (key2046, -1), (key2051, 2), (key2023, 2), (key2052, 2), (key2128, 1), (key2138, 1), (key2014, 1), (key2141, 1), (key2018, 1), (key2133, 1), (key2138, -2), (key2023, -2), (key2141, -2), (key2043, -1), (key2051, -1), (key2014, -1), (key2052, -1), (key2018, -1), (key2046, -1), (key2128, 1), (key2138, 1), (key2014, 1), (key2141, 1), (key2018, 1), (key2133, 1), (key2051, 2), (key2023, 2), (key2052, 2), (key2138, -2), (key2023, -2), (key2141, -2)]

def rawRow17334 : Integer.Sparse Key := [(key2051, -1), (key2043, -1), (key2052, -1), (key2014, -1), (key2046, -1), (key2018, -1), (key2051, 2), (key2052, 2), (key2023, 2), (key2138, 1), (key2128, 1), (key2141, 1), (key2014, 1), (key2133, 1), (key2018, 1), (key2138, -2), (key2141, -2), (key2023, -2), (key2051, -1), (key2043, -1), (key2052, -1), (key2014, -1), (key2046, -1), (key2018, -1), (key2138, 1), (key2128, 1), (key2141, 1), (key2014, 1), (key2133, 1), (key2018, 1), (key2051, 2), (key2052, 2), (key2023, 2), (key2138, -2), (key2141, -2), (key2023, -2)]

def rawRow17335 : Integer.Sparse Key := [(key2046, -1), (key2052, -1), (key2018, -1), (key2051, -1), (key2014, -1), (key2043, -1), (key2052, 2), (key2023, 2), (key2051, 2), (key2133, 1), (key2141, 1), (key2018, 1), (key2138, 1), (key2014, 1), (key2128, 1), (key2141, -2), (key2023, -2), (key2138, -2), (key2046, -1), (key2052, -1), (key2018, -1), (key2051, -1), (key2014, -1), (key2043, -1), (key2133, 1), (key2141, 1), (key2018, 1), (key2138, 1), (key2014, 1), (key2128, 1), (key2052, 2), (key2023, 2), (key2051, 2), (key2141, -2), (key2023, -2), (key2138, -2)]

def rawRow17336 : Integer.Sparse Key := [(key2052, -1), (key2046, -1), (key2051, -1), (key2018, -1), (key2043, -1), (key2014, -1), (key2052, 2), (key2051, 2), (key2023, 2), (key2141, 1), (key2133, 1), (key2138, 1), (key2018, 1), (key2128, 1), (key2014, 1), (key2141, -2), (key2138, -2), (key2023, -2), (key2052, -1), (key2046, -1), (key2051, -1), (key2018, -1), (key2043, -1), (key2014, -1), (key2141, 1), (key2133, 1), (key2138, 1), (key2018, 1), (key2128, 1), (key2014, 1), (key2052, 2), (key2051, 2), (key2023, 2), (key2141, -2), (key2138, -2), (key2023, -2)]

def rawRow17337 : Integer.Sparse Key := [(key2014, -1), (key2023, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2052, -1), (key2018, 2), (key2018, 2), (key2046, 2), (key2014, 1), (key2023, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2141, 1), (key2018, -2), (key2018, -2), (key2133, -2), (key2128, -1), (key2138, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2221, -1), (key2043, 1), (key2051, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2222, 1), (key2138, 2), (key2138, 2), (key2221, 2), (key2051, -2), (key2051, -2), (key2222, -2)]

def rawRow17338 : Integer.Sparse Key := [(key2023, -1), (key2014, -1), (key2052, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2018, 2), (key2046, 2), (key2018, 2), (key2023, 1), (key2014, 1), (key2141, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2018, -2), (key2133, -2), (key2018, -2), (key2138, -1), (key2128, -1), (key2221, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2051, 1), (key2043, 1), (key2222, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2138, 2), (key2221, 2), (key2138, 2), (key2051, -2), (key2222, -2), (key2051, -2)]

def rawRow17339 : Integer.Sparse Key := [(key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2046, 2), (key2018, 2), (key2018, 2), (key2141, 1), (key2141, 1), (key2023, 1), (key2023, 1), (key2014, 1), (key2014, 1), (key2133, -2), (key2018, -2), (key2018, -2), (key2221, -1), (key2221, -1), (key2138, -1), (key2138, -1), (key2128, -1), (key2128, -1), (key2222, 1), (key2222, 1), (key2051, 1), (key2051, 1), (key2043, 1), (key2043, 1), (key2221, 2), (key2138, 2), (key2138, 2), (key2222, -2), (key2051, -2), (key2051, -2)]

def rawRow17340 : Integer.Sparse Key := [(key2018, -1), (key2023, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2051, -1), (key2014, 2), (key2014, 2), (key2043, 2), (key2018, 1), (key2023, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2138, 1), (key2014, -2), (key2014, -2), (key2128, -2), (key2133, -1), (key2141, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2222, -1), (key2046, 1), (key2052, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2221, 1), (key2141, 2), (key2141, 2), (key2222, 2), (key2052, -2), (key2052, -2), (key2221, -2)]

def rawRow17341 : Integer.Sparse Key := [(key2023, -1), (key2018, -1), (key2051, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2014, 2), (key2043, 2), (key2014, 2), (key2023, 1), (key2018, 1), (key2138, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2014, -2), (key2128, -2), (key2014, -2), (key2141, -1), (key2133, -1), (key2222, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2052, 1), (key2046, 1), (key2221, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2141, 2), (key2222, 2), (key2141, 2), (key2052, -2), (key2221, -2), (key2052, -2)]

def rawRow17342 : Integer.Sparse Key := [(key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2043, 2), (key2014, 2), (key2014, 2), (key2138, 1), (key2138, 1), (key2023, 1), (key2023, 1), (key2018, 1), (key2018, 1), (key2128, -2), (key2014, -2), (key2014, -2), (key2222, -1), (key2222, -1), (key2141, -1), (key2141, -1), (key2133, -1), (key2133, -1), (key2221, 1), (key2221, 1), (key2052, 1), (key2052, 1), (key2046, 1), (key2046, 1), (key2222, 2), (key2141, 2), (key2141, 2), (key2221, -2), (key2052, -2), (key2052, -2)]

def rawRow17343 : Integer.Sparse Key := [(key2128, -1), (key2138, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2221, -1), (key2138, 2), (key2138, 2), (key2221, 2), (key2043, 1), (key2051, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2222, 1), (key2051, -2), (key2051, -2), (key2222, -2), (key2014, -1), (key2023, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2052, -1), (key2014, 1), (key2023, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2141, 1), (key2018, 2), (key2018, 2), (key2046, 2), (key2018, -2), (key2018, -2), (key2133, -2)]

def rawRow17344 : Integer.Sparse Key := [(key2138, -1), (key2128, -1), (key2221, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2138, 2), (key2221, 2), (key2138, 2), (key2051, 1), (key2043, 1), (key2222, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2051, -2), (key2222, -2), (key2051, -2), (key2023, -1), (key2014, -1), (key2052, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2023, 1), (key2014, 1), (key2141, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2018, 2), (key2046, 2), (key2018, 2), (key2018, -2), (key2133, -2), (key2018, -2)]

def rawRow17345 : Integer.Sparse Key := [(key2221, -1), (key2221, -1), (key2138, -1), (key2138, -1), (key2128, -1), (key2128, -1), (key2221, 2), (key2138, 2), (key2138, 2), (key2222, 1), (key2222, 1), (key2051, 1), (key2051, 1), (key2043, 1), (key2043, 1), (key2222, -2), (key2051, -2), (key2051, -2), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2141, 1), (key2141, 1), (key2023, 1), (key2023, 1), (key2014, 1), (key2014, 1), (key2046, 2), (key2018, 2), (key2018, 2), (key2133, -2), (key2018, -2), (key2018, -2)]

def rawRow17346 : Integer.Sparse Key := [(key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2128, 2), (key2128, 2), (key2128, 2), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2043, -2), (key2043, -2), (key2043, -2), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2133, 2), (key2133, 2), (key2133, 2), (key2046, -2), (key2046, -2), (key2046, -2)]

def rawRow17347 : Integer.Sparse Key := [(key2133, -1), (key2141, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2222, -1), (key2141, 2), (key2141, 2), (key2222, 2), (key2046, 1), (key2052, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2221, 1), (key2052, -2), (key2052, -2), (key2221, -2), (key2018, -1), (key2023, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2051, -1), (key2018, 1), (key2023, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2138, 1), (key2014, 2), (key2014, 2), (key2043, 2), (key2014, -2), (key2014, -2), (key2128, -2)]

def rawRow17348 : Integer.Sparse Key := [(key2141, -1), (key2133, -1), (key2222, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2141, 2), (key2222, 2), (key2141, 2), (key2052, 1), (key2046, 1), (key2221, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2052, -2), (key2221, -2), (key2052, -2), (key2023, -1), (key2018, -1), (key2051, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2023, 1), (key2018, 1), (key2138, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2014, 2), (key2043, 2), (key2014, 2), (key2014, -2), (key2128, -2), (key2014, -2)]

def rawRow17349 : Integer.Sparse Key := [(key2222, -1), (key2222, -1), (key2141, -1), (key2141, -1), (key2133, -1), (key2133, -1), (key2222, 2), (key2141, 2), (key2141, 2), (key2221, 1), (key2221, 1), (key2052, 1), (key2052, 1), (key2046, 1), (key2046, 1), (key2221, -2), (key2052, -2), (key2052, -2), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2138, 1), (key2138, 1), (key2023, 1), (key2023, 1), (key2018, 1), (key2018, 1), (key2043, 2), (key2014, 2), (key2014, 2), (key2128, -2), (key2014, -2), (key2014, -2)]

def rawRow17350 : Integer.Sparse Key := [(key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2133, 2), (key2133, 2), (key2133, 2), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2046, -2), (key2046, -2), (key2046, -2), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2128, 2), (key2128, 2), (key2128, 2), (key2043, -2), (key2043, -2), (key2043, -2)]

def rawRow17351 : Integer.Sparse Key := [(key2017, 2), (key2137, 2), (key2142, 2), (key2022, -1), (key2024, -1), (key2137, -1), (key2142, -1), (key2172, -1), (key2173, -1), (key2017, 2), (key2137, 2), (key2142, 2), (key2050, -1), (key2053, -1), (key2137, -1), (key2142, -1), (key2264, -1), (key2265, -1), (key2022, -1), (key2024, -1), (key2137, -1), (key2142, -1), (key2172, -1), (key2173, -1), (key2050, -1), (key2053, -1), (key2137, -1), (key2142, -1), (key2264, -1), (key2265, -1), (key2075, 2), (key2076, 2), (key2172, 2), (key2173, 2), (key2264, 2), (key2265, 2)]

def rawRow17352 : Integer.Sparse Key := [(key2017, 2), (key2142, 2), (key2137, 2), (key2024, -1), (key2022, -1), (key2142, -1), (key2137, -1), (key2173, -1), (key2172, -1), (key2017, 2), (key2142, 2), (key2137, 2), (key2053, -1), (key2050, -1), (key2142, -1), (key2137, -1), (key2265, -1), (key2264, -1), (key2024, -1), (key2022, -1), (key2142, -1), (key2137, -1), (key2173, -1), (key2172, -1), (key2053, -1), (key2050, -1), (key2142, -1), (key2137, -1), (key2265, -1), (key2264, -1), (key2076, 2), (key2075, 2), (key2173, 2), (key2172, 2), (key2265, 2), (key2264, 2)]

def rawRow17353 : Integer.Sparse Key := [(key2137, 2), (key2017, 2), (key2142, 2), (key2137, -1), (key2172, -1), (key2022, -1), (key2173, -1), (key2024, -1), (key2142, -1), (key2137, 2), (key2017, 2), (key2142, 2), (key2137, -1), (key2264, -1), (key2050, -1), (key2265, -1), (key2053, -1), (key2142, -1), (key2137, -1), (key2172, -1), (key2022, -1), (key2173, -1), (key2024, -1), (key2142, -1), (key2137, -1), (key2264, -1), (key2050, -1), (key2265, -1), (key2053, -1), (key2142, -1), (key2172, 2), (key2264, 2), (key2075, 2), (key2265, 2), (key2076, 2), (key2173, 2)]

def rawRow17354 : Integer.Sparse Key := [(key2137, 2), (key2142, 2), (key2017, 2), (key2172, -1), (key2137, -1), (key2173, -1), (key2022, -1), (key2142, -1), (key2024, -1), (key2137, 2), (key2142, 2), (key2017, 2), (key2264, -1), (key2137, -1), (key2265, -1), (key2050, -1), (key2142, -1), (key2053, -1), (key2172, -1), (key2137, -1), (key2173, -1), (key2022, -1), (key2142, -1), (key2024, -1), (key2264, -1), (key2137, -1), (key2265, -1), (key2050, -1), (key2142, -1), (key2053, -1), (key2264, 2), (key2172, 2), (key2265, 2), (key2075, 2), (key2173, 2), (key2076, 2)]

def rawRow17355 : Integer.Sparse Key := [(key2142, 2), (key2017, 2), (key2137, 2), (key2142, -1), (key2173, -1), (key2024, -1), (key2172, -1), (key2022, -1), (key2137, -1), (key2142, 2), (key2017, 2), (key2137, 2), (key2142, -1), (key2265, -1), (key2053, -1), (key2264, -1), (key2050, -1), (key2137, -1), (key2142, -1), (key2173, -1), (key2024, -1), (key2172, -1), (key2022, -1), (key2137, -1), (key2142, -1), (key2265, -1), (key2053, -1), (key2264, -1), (key2050, -1), (key2137, -1), (key2173, 2), (key2265, 2), (key2076, 2), (key2264, 2), (key2075, 2), (key2172, 2)]

def rawRow17356 : Integer.Sparse Key := [(key2142, 2), (key2137, 2), (key2017, 2), (key2173, -1), (key2142, -1), (key2172, -1), (key2024, -1), (key2137, -1), (key2022, -1), (key2142, 2), (key2137, 2), (key2017, 2), (key2265, -1), (key2142, -1), (key2264, -1), (key2053, -1), (key2137, -1), (key2050, -1), (key2173, -1), (key2142, -1), (key2172, -1), (key2024, -1), (key2137, -1), (key2022, -1), (key2265, -1), (key2142, -1), (key2264, -1), (key2053, -1), (key2137, -1), (key2050, -1), (key2265, 2), (key2173, 2), (key2264, 2), (key2076, 2), (key2172, 2), (key2075, 2)]

def rawRow17357 : Integer.Sparse Key := [(key2022, 2), (key2022, 2), (key2173, 2), (key2017, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2142, -1), (key2050, 2), (key2050, 2), (key2265, 2), (key2017, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2142, -1), (key2050, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2265, -1), (key2022, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2173, -1), (key2024, 2), (key2053, 2), (key2024, 2), (key2142, 2), (key2053, 2), (key2142, 2)]

def rawRow17358 : Integer.Sparse Key := [(key2022, 2), (key2173, 2), (key2022, 2), (key2024, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2050, 2), (key2265, 2), (key2050, 2), (key2053, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2053, 2), (key2024, 2), (key2142, 2), (key2024, 2), (key2142, 2), (key2053, 2)]

def rawRow17359 : Integer.Sparse Key := [(key2173, 2), (key2022, 2), (key2022, 2), (key2142, -1), (key2142, -1), (key2024, -1), (key2024, -1), (key2017, -1), (key2017, -1), (key2265, 2), (key2050, 2), (key2050, 2), (key2142, -1), (key2142, -1), (key2053, -1), (key2053, -1), (key2017, -1), (key2017, -1), (key2265, -1), (key2265, -1), (key2075, -1), (key2075, -1), (key2050, -1), (key2050, -1), (key2173, -1), (key2173, -1), (key2076, -1), (key2076, -1), (key2022, -1), (key2022, -1), (key2142, 2), (key2142, 2), (key2053, 2), (key2053, 2), (key2024, 2), (key2024, 2)]

def rawRow17360 : Integer.Sparse Key := [(key2024, 2), (key2024, 2), (key2172, 2), (key2017, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2137, -1), (key2053, 2), (key2053, 2), (key2264, 2), (key2017, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2137, -1), (key2053, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2264, -1), (key2024, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2172, -1), (key2022, 2), (key2050, 2), (key2022, 2), (key2137, 2), (key2050, 2), (key2137, 2)]

def rawRow17361 : Integer.Sparse Key := [(key2024, 2), (key2172, 2), (key2024, 2), (key2022, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2053, 2), (key2264, 2), (key2053, 2), (key2050, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2050, 2), (key2022, 2), (key2137, 2), (key2022, 2), (key2137, 2), (key2050, 2)]

def rawRow17362 : Integer.Sparse Key := [(key2172, 2), (key2024, 2), (key2024, 2), (key2137, -1), (key2137, -1), (key2022, -1), (key2022, -1), (key2017, -1), (key2017, -1), (key2264, 2), (key2053, 2), (key2053, 2), (key2137, -1), (key2137, -1), (key2050, -1), (key2050, -1), (key2017, -1), (key2017, -1), (key2264, -1), (key2264, -1), (key2076, -1), (key2076, -1), (key2053, -1), (key2053, -1), (key2172, -1), (key2172, -1), (key2075, -1), (key2075, -1), (key2024, -1), (key2024, -1), (key2137, 2), (key2137, 2), (key2050, 2), (key2050, 2), (key2022, 2), (key2022, 2)]

def rawRow17363 : Integer.Sparse Key := [(key2050, 2), (key2050, 2), (key2265, 2), (key2050, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2265, -1), (key2022, 2), (key2022, 2), (key2173, 2), (key2022, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2173, -1), (key2017, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2142, -1), (key2017, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2142, -1), (key2024, 2), (key2053, 2), (key2024, 2), (key2142, 2), (key2053, 2), (key2142, 2)]

def rawRow17364 : Integer.Sparse Key := [(key2050, 2), (key2265, 2), (key2050, 2), (key2075, -1), (key2050, -1), (key2265, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2022, 2), (key2173, 2), (key2022, 2), (key2076, -1), (key2022, -1), (key2173, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2053, 2), (key2024, 2), (key2142, 2), (key2024, 2), (key2142, 2), (key2053, 2)]

def rawRow17365 : Integer.Sparse Key := [(key2265, 2), (key2050, 2), (key2050, 2), (key2265, -1), (key2265, -1), (key2075, -1), (key2075, -1), (key2050, -1), (key2050, -1), (key2173, 2), (key2022, 2), (key2022, 2), (key2173, -1), (key2173, -1), (key2076, -1), (key2076, -1), (key2022, -1), (key2022, -1), (key2142, -1), (key2142, -1), (key2024, -1), (key2024, -1), (key2017, -1), (key2017, -1), (key2142, -1), (key2142, -1), (key2053, -1), (key2053, -1), (key2017, -1), (key2017, -1), (key2142, 2), (key2142, 2), (key2053, 2), (key2053, 2), (key2024, 2), (key2024, 2)]

def rawRow17366 : Integer.Sparse Key := [(key2075, 2), (key2075, 2), (key2075, 2), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2076, 2), (key2076, 2), (key2076, 2), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2)]

def rawRow17367 : Integer.Sparse Key := [(key2053, 2), (key2053, 2), (key2264, 2), (key2053, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2264, -1), (key2024, 2), (key2024, 2), (key2172, 2), (key2024, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2172, -1), (key2017, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2137, -1), (key2017, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2137, -1), (key2022, 2), (key2050, 2), (key2022, 2), (key2137, 2), (key2050, 2), (key2137, 2)]

def rawRow17368 : Integer.Sparse Key := [(key2053, 2), (key2264, 2), (key2053, 2), (key2076, -1), (key2053, -1), (key2264, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2024, 2), (key2172, 2), (key2024, 2), (key2075, -1), (key2024, -1), (key2172, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2050, 2), (key2022, 2), (key2137, 2), (key2022, 2), (key2137, 2), (key2050, 2)]

def rawRow17369 : Integer.Sparse Key := [(key2264, 2), (key2053, 2), (key2053, 2), (key2264, -1), (key2264, -1), (key2076, -1), (key2076, -1), (key2053, -1), (key2053, -1), (key2172, 2), (key2024, 2), (key2024, 2), (key2172, -1), (key2172, -1), (key2075, -1), (key2075, -1), (key2024, -1), (key2024, -1), (key2137, -1), (key2137, -1), (key2022, -1), (key2022, -1), (key2017, -1), (key2017, -1), (key2137, -1), (key2137, -1), (key2050, -1), (key2050, -1), (key2017, -1), (key2017, -1), (key2137, 2), (key2137, 2), (key2050, 2), (key2050, 2), (key2022, 2), (key2022, 2)]

def rawRow17370 : Integer.Sparse Key := [(key2076, 2), (key2076, 2), (key2076, 2), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2075, 2), (key2075, 2), (key2075, 2), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2)]

def rawRow17371 : Integer.Sparse Key := [(key770, 4), (key774, 4), (key783, 4), (key770, -2), (key774, -2), (key797, -2), (key834, -2), (key808, -2), (key837, -2), (key770, -2), (key774, -2), (key797, -2), (key834, -2), (key808, -2), (key837, -2), (key797, 4), (key834, 4), (key932, 4)]

def rawRow17372 : Integer.Sparse Key := [(key774, 4), (key770, 4), (key783, 4), (key774, -2), (key770, -2), (key834, -2), (key797, -2), (key837, -2), (key808, -2), (key774, -2), (key770, -2), (key834, -2), (key797, -2), (key837, -2), (key808, -2), (key834, 4), (key797, 4), (key932, 4)]

def rawRow17373 : Integer.Sparse Key := [(key770, 4), (key783, 4), (key774, 4), (key797, -2), (key808, -2), (key770, -2), (key837, -2), (key774, -2), (key834, -2), (key797, -2), (key808, -2), (key770, -2), (key837, -2), (key774, -2), (key834, -2), (key797, 4), (key932, 4), (key834, 4)]

def rawRow17374 : Integer.Sparse Key := [(key783, 4), (key770, 4), (key774, 4), (key808, -2), (key797, -2), (key837, -2), (key770, -2), (key834, -2), (key774, -2), (key808, -2), (key797, -2), (key837, -2), (key770, -2), (key834, -2), (key774, -2), (key932, 4), (key797, 4), (key834, 4)]

def rawRow17375 : Integer.Sparse Key := [(key774, 4), (key783, 4), (key770, 4), (key834, -2), (key837, -2), (key774, -2), (key808, -2), (key770, -2), (key797, -2), (key834, -2), (key837, -2), (key774, -2), (key808, -2), (key770, -2), (key797, -2), (key834, 4), (key932, 4), (key797, 4)]

def rawRow17376 : Integer.Sparse Key := [(key783, 4), (key774, 4), (key770, 4), (key837, -2), (key834, -2), (key808, -2), (key774, -2), (key797, -2), (key770, -2), (key837, -2), (key834, -2), (key808, -2), (key774, -2), (key797, -2), (key770, -2), (key932, 4), (key834, 4), (key797, 4)]

def rawRow17377 : Integer.Sparse Key := [(key797, 4), (key808, 4), (key808, 4), (key770, -2), (key783, -2), (key770, -2), (key837, -2), (key783, -2), (key837, -2), (key797, -2), (key808, -2), (key797, -2), (key932, -2), (key808, -2), (key932, -2), (key770, 4), (key837, 4), (key837, 4)]

def rawRow17378 : Integer.Sparse Key := [(key808, 4), (key797, 4), (key808, 4), (key783, -2), (key770, -2), (key837, -2), (key770, -2), (key837, -2), (key783, -2), (key808, -2), (key797, -2), (key932, -2), (key797, -2), (key932, -2), (key808, -2), (key837, 4), (key770, 4), (key837, 4)]

def rawRow17379 : Integer.Sparse Key := [(key808, 4), (key808, 4), (key797, 4), (key837, -2), (key837, -2), (key783, -2), (key783, -2), (key770, -2), (key770, -2), (key932, -2), (key932, -2), (key808, -2), (key808, -2), (key797, -2), (key797, -2), (key837, 4), (key837, 4), (key770, 4)]

def rawRow17380 : Integer.Sparse Key := [(key834, 4), (key837, 4), (key837, 4), (key774, -2), (key783, -2), (key774, -2), (key808, -2), (key783, -2), (key808, -2), (key834, -2), (key837, -2), (key834, -2), (key932, -2), (key837, -2), (key932, -2), (key774, 4), (key808, 4), (key808, 4)]

def rawRow17381 : Integer.Sparse Key := [(key837, 4), (key834, 4), (key837, 4), (key783, -2), (key774, -2), (key808, -2), (key774, -2), (key808, -2), (key783, -2), (key837, -2), (key834, -2), (key932, -2), (key834, -2), (key932, -2), (key837, -2), (key808, 4), (key774, 4), (key808, 4)]

def rawRow17382 : Integer.Sparse Key := [(key837, 4), (key837, 4), (key834, 4), (key808, -2), (key808, -2), (key783, -2), (key783, -2), (key774, -2), (key774, -2), (key932, -2), (key932, -2), (key837, -2), (key837, -2), (key834, -2), (key834, -2), (key808, 4), (key808, 4), (key774, 4)]

def rawRow17383 : Integer.Sparse Key := [(key797, 4), (key808, 4), (key808, 4), (key797, -2), (key808, -2), (key797, -2), (key932, -2), (key808, -2), (key932, -2), (key770, -2), (key783, -2), (key770, -2), (key837, -2), (key783, -2), (key837, -2), (key770, 4), (key837, 4), (key837, 4)]

def rawRow17384 : Integer.Sparse Key := [(key808, 4), (key797, 4), (key808, 4), (key808, -2), (key797, -2), (key932, -2), (key797, -2), (key932, -2), (key808, -2), (key783, -2), (key770, -2), (key837, -2), (key770, -2), (key837, -2), (key783, -2), (key837, 4), (key770, 4), (key837, 4)]

def rawRow17385 : Integer.Sparse Key := [(key808, 4), (key808, 4), (key797, 4), (key932, -2), (key932, -2), (key808, -2), (key808, -2), (key797, -2), (key797, -2), (key837, -2), (key837, -2), (key783, -2), (key783, -2), (key770, -2), (key770, -2), (key837, 4), (key837, 4), (key770, 4)]

def rawRow17386 : Integer.Sparse Key := [(key932, 4), (key932, 4), (key932, 4), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key783, 4), (key783, 4), (key783, 4)]

def rawRow17387 : Integer.Sparse Key := [(key834, 4), (key837, 4), (key837, 4), (key834, -2), (key837, -2), (key834, -2), (key932, -2), (key837, -2), (key932, -2), (key774, -2), (key783, -2), (key774, -2), (key808, -2), (key783, -2), (key808, -2), (key774, 4), (key808, 4), (key808, 4)]

def rawRow17388 : Integer.Sparse Key := [(key837, 4), (key834, 4), (key837, 4), (key837, -2), (key834, -2), (key932, -2), (key834, -2), (key932, -2), (key837, -2), (key783, -2), (key774, -2), (key808, -2), (key774, -2), (key808, -2), (key783, -2), (key808, 4), (key774, 4), (key808, 4)]

def rawRow17389 : Integer.Sparse Key := [(key837, 4), (key837, 4), (key834, 4), (key932, -2), (key932, -2), (key837, -2), (key837, -2), (key834, -2), (key834, -2), (key808, -2), (key808, -2), (key783, -2), (key783, -2), (key774, -2), (key774, -2), (key808, 4), (key808, 4), (key774, 4)]

def rawRow17390 : Integer.Sparse Key := [(key932, 4), (key932, 4), (key932, 4), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key783, 4), (key783, 4), (key783, 4)]

def rawRow17391 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key761, 2), (key766, 2), (key793, 2), (key768, 2), (key769, 2), (key793, 2), (key761, 2), (key766, 2), (key793, 2), (key793, -6), (key768, 2), (key769, 2), (key793, 2), (key793, -6)]

def rawRow17392 : Integer.Sparse Key := [(key759, -2), (key757, -2), (key766, -2), (key761, -2), (key769, -2), (key768, -2), (key766, 2), (key761, 2), (key793, 2), (key769, 2), (key768, 2), (key793, 2), (key766, 2), (key761, 2), (key793, 2), (key793, -6), (key769, 2), (key768, 2), (key793, 2), (key793, -6)]

def rawRow17393 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key757, -2), (key769, -2), (key759, -2), (key766, -2), (key761, 2), (key793, 2), (key766, 2), (key768, 2), (key793, 2), (key769, 2), (key761, 2), (key793, 2), (key766, 2), (key793, -6), (key768, 2), (key793, 2), (key769, 2), (key793, -6)]

def rawRow17394 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key769, -2), (key757, -2), (key766, -2), (key759, -2), (key793, 2), (key761, 2), (key766, 2), (key793, 2), (key768, 2), (key769, 2), (key793, 2), (key761, 2), (key766, 2), (key793, -6), (key793, 2), (key768, 2), (key769, 2), (key793, -6)]

def rawRow17395 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key759, -2), (key766, -2), (key757, -2), (key761, -2), (key766, 2), (key793, 2), (key761, 2), (key769, 2), (key793, 2), (key768, 2), (key766, 2), (key793, 2), (key761, 2), (key793, -6), (key769, 2), (key793, 2), (key768, 2), (key793, -6)]

def rawRow17396 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key766, -2), (key759, -2), (key761, -2), (key757, -2), (key793, 2), (key766, 2), (key761, 2), (key793, 2), (key769, 2), (key768, 2), (key793, 2), (key766, 2), (key761, 2), (key793, -6), (key793, 2), (key769, 2), (key768, 2), (key793, -6)]

def rawRow17397 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key761, -2), (key793, -2), (key766, -2), (key793, -2), (key757, 2), (key769, 2), (key769, 2), (key759, 2), (key766, 2), (key766, 2), (key761, 2), (key793, 2), (key793, 2), (key766, -6), (key768, 2), (key793, 2), (key793, 2), (key769, -6)]

def rawRow17398 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key793, -2), (key761, -2), (key793, -2), (key766, -2), (key769, 2), (key757, 2), (key769, 2), (key766, 2), (key759, 2), (key766, 2), (key793, 2), (key761, 2), (key793, 2), (key766, -6), (key793, 2), (key768, 2), (key793, 2), (key769, -6)]

def rawRow17399 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key766, -2), (key766, -2), (key761, -2), (key761, -2), (key769, 2), (key769, 2), (key757, 2), (key766, 2), (key766, 2), (key759, 2), (key793, 2), (key793, 2), (key761, 2), (key766, -6), (key793, 2), (key793, 2), (key768, 2), (key769, -6)]

def rawRow17400 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key768, -2), (key793, -2), (key769, -2), (key793, -2), (key759, 2), (key766, 2), (key766, 2), (key757, 2), (key761, 2), (key761, 2), (key766, 2), (key793, 2), (key793, 2), (key761, -6), (key769, 2), (key793, 2), (key793, 2), (key768, -6)]

def rawRow17401 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key793, -2), (key768, -2), (key793, -2), (key769, -2), (key766, 2), (key759, 2), (key766, 2), (key761, 2), (key757, 2), (key761, 2), (key793, 2), (key766, 2), (key793, 2), (key761, -6), (key793, 2), (key769, 2), (key793, 2), (key768, -6)]

def rawRow17402 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key769, -2), (key769, -2), (key768, -2), (key768, -2), (key766, 2), (key766, 2), (key759, 2), (key761, 2), (key761, 2), (key757, 2), (key793, 2), (key793, 2), (key766, 2), (key761, -6), (key793, 2), (key793, 2), (key769, 2), (key768, -6)]

def rawRow17403 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key761, -2), (key793, -2), (key766, -2), (key793, -2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key793, 2), (key793, 2), (key757, 2), (key769, 2), (key769, 2), (key769, -6), (key759, 2), (key766, 2), (key766, 2), (key766, -6)]

def rawRow17404 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key793, -2), (key761, -2), (key793, -2), (key766, -2), (key793, 2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key793, 2), (key769, 2), (key757, 2), (key769, 2), (key769, -6), (key766, 2), (key759, 2), (key766, 2), (key766, -6)]

def rawRow17405 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key766, -2), (key766, -2), (key761, -2), (key761, -2), (key793, 2), (key793, 2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key769, 2), (key769, 2), (key757, 2), (key769, -6), (key766, 2), (key766, 2), (key759, 2), (key766, -6)]

def rawRow17406 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key766, 2), (key766, 2), (key766, 2), (key761, 2), (key761, 2), (key761, 2), (key769, 2), (key769, 2), (key769, 2), (key757, -6), (key766, 2), (key766, 2), (key766, 2), (key759, -6)]

def rawRow17407 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key768, -2), (key793, -2), (key769, -2), (key793, -2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key793, 2), (key793, 2), (key759, 2), (key766, 2), (key766, 2), (key766, -6), (key757, 2), (key761, 2), (key761, 2), (key761, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17408 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key793, -2), (key768, -2), (key793, -2), (key769, -2), (key793, 2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key793, 2), (key766, 2), (key759, 2), (key766, 2), (key766, -6), (key761, 2), (key757, 2), (key761, 2), (key761, -6)]

def rawRow17409 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key769, -2), (key769, -2), (key768, -2), (key768, -2), (key793, 2), (key793, 2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key766, 2), (key766, 2), (key759, 2), (key766, -6), (key761, 2), (key761, 2), (key757, 2), (key761, -6)]

def rawRow17410 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key769, 2), (key769, 2), (key769, 2), (key768, 2), (key768, 2), (key768, 2), (key766, 2), (key766, 2), (key766, 2), (key759, -6), (key761, 2), (key761, 2), (key761, 2), (key757, -6)]

def rawRow17411 : Integer.Sparse Key := [(key1854, 4), (key1887, 4), (key1887, 4), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1890, -2), (key1858, 4), (key1890, 4), (key1890, 4)]

def rawRow17412 : Integer.Sparse Key := [(key1887, 4), (key1854, 4), (key1887, 4), (key1887, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1890, 4), (key1858, 4), (key1890, 4)]

def rawRow17413 : Integer.Sparse Key := [(key1887, 4), (key1887, 4), (key1854, 4), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1890, 4), (key1890, 4), (key1858, 4)]

def rawRow17414 : Integer.Sparse Key := [(key1856, 4), (key1856, 4), (key1890, 4), (key1854, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1890, -2), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17415 : Integer.Sparse Key := [(key1856, 4), (key1890, 4), (key1856, 4), (key1856, -2), (key1854, -2), (key1887, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1856, 4), (key1887, 4), (key1856, 4)]

def rawRow17416 : Integer.Sparse Key := [(key1890, 4), (key1856, 4), (key1856, 4), (key1887, -2), (key1887, -2), (key1856, -2), (key1856, -2), (key1854, -2), (key1854, -2), (key1890, -2), (key1890, -2), (key1858, -2), (key1858, -2), (key1856, -2), (key1856, -2), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17417 : Integer.Sparse Key := [(key1856, 4), (key1856, 4), (key1890, 4), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1890, -2), (key1854, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1887, -2), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17418 : Integer.Sparse Key := [(key1856, 4), (key1890, 4), (key1856, 4), (key1858, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1856, 4), (key1887, 4), (key1856, 4)]

def rawRow17419 : Integer.Sparse Key := [(key1890, 4), (key1856, 4), (key1856, 4), (key1890, -2), (key1890, -2), (key1858, -2), (key1858, -2), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1856, -2), (key1856, -2), (key1854, -2), (key1854, -2), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17420 : Integer.Sparse Key := [(key1858, 4), (key1858, 4), (key1858, 4), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1854, 4), (key1854, 4), (key1854, 4)]

def rawRow17421 : Integer.Sparse Key := [(key620, -2), (key620, -2), (key624, -2), (key624, 6), (key620, -2), (key620, -2), (key624, -2), (key620, 2), (key620, 2), (key646, 2), (key646, 2), (key652, 2), (key652, 2), (key624, -2), (key652, -2), (key652, -2), (key624, 6), (key624, -2), (key652, -2), (key652, -2)]

def rawRow17422 : Integer.Sparse Key := [(key620, -2), (key624, -2), (key620, -2), (key624, 6), (key620, -2), (key624, -2), (key620, -2), (key646, 2), (key652, 2), (key620, 2), (key652, 2), (key620, 2), (key646, 2), (key652, -2), (key624, -2), (key652, -2), (key624, 6), (key652, -2), (key624, -2), (key652, -2)]

def rawRow17423 : Integer.Sparse Key := [(key624, -2), (key620, -2), (key620, -2), (key624, 6), (key624, -2), (key620, -2), (key620, -2), (key652, 2), (key646, 2), (key652, 2), (key620, 2), (key646, 2), (key620, 2), (key652, -2), (key652, -2), (key624, -2), (key624, 6), (key652, -2), (key652, -2), (key624, -2)]

def rawRow17424 : Integer.Sparse Key := [(key620, -2), (key624, -2), (key624, -2), (key620, 6), (key646, -2), (key652, -2), (key652, -2), (key620, 2), (key624, 2), (key620, 2), (key652, 2), (key624, 2), (key652, 2), (key620, -2), (key620, -2), (key646, -2), (key652, 6), (key624, -2), (key624, -2), (key652, -2)]

def rawRow17425 : Integer.Sparse Key := [(key624, -2), (key620, -2), (key624, -2), (key620, 6), (key652, -2), (key646, -2), (key652, -2), (key624, 2), (key620, 2), (key652, 2), (key620, 2), (key652, 2), (key624, 2), (key620, -2), (key646, -2), (key620, -2), (key652, 6), (key624, -2), (key652, -2), (key624, -2)]

def rawRow17426 : Integer.Sparse Key := [(key624, -2), (key624, -2), (key620, -2), (key620, 6), (key652, -2), (key652, -2), (key646, -2), (key652, 2), (key652, 2), (key624, 2), (key624, 2), (key620, 2), (key620, 2), (key646, -2), (key620, -2), (key620, -2), (key652, 6), (key652, -2), (key624, -2), (key624, -2)]

def rawRow17427 : Integer.Sparse Key := [(key646, -2), (key652, -2), (key652, -2), (key652, 6), (key620, -2), (key624, -2), (key624, -2), (key620, 2), (key624, 2), (key620, 2), (key652, 2), (key624, 2), (key652, 2), (key624, -2), (key624, -2), (key652, -2), (key620, 6), (key620, -2), (key620, -2), (key646, -2)]

def rawRow17428 : Integer.Sparse Key := [(key652, -2), (key646, -2), (key652, -2), (key652, 6), (key624, -2), (key620, -2), (key624, -2), (key624, 2), (key620, 2), (key652, 2), (key620, 2), (key652, 2), (key624, 2), (key624, -2), (key652, -2), (key624, -2), (key620, 6), (key620, -2), (key646, -2), (key620, -2)]

def rawRow17429 : Integer.Sparse Key := [(key652, -2), (key652, -2), (key646, -2), (key652, 6), (key624, -2), (key624, -2), (key620, -2), (key652, 2), (key652, 2), (key624, 2), (key624, 2), (key620, 2), (key620, 2), (key652, -2), (key624, -2), (key624, -2), (key620, 6), (key646, -2), (key620, -2), (key620, -2)]

def rawRow17430 : Integer.Sparse Key := [(key652, -2), (key652, -2), (key652, -2), (key646, 6), (key652, -2), (key652, -2), (key652, -2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key620, -2), (key620, -2), (key620, -2), (key646, 6), (key620, -2), (key620, -2), (key620, -2)]

def rawRow17431 : Integer.Sparse Key := [(key1853, -2), (key1853, -2), (key1857, -2), (key1857, 6), (key1853, -2), (key1853, -2), (key1857, -2), (key1853, 2), (key1853, 2), (key1885, 2), (key1885, 2), (key1888, 2), (key1888, 2), (key1857, -2), (key1888, -2), (key1888, -2), (key1857, 6), (key1857, -2), (key1888, -2), (key1888, -2)]

def rawRow17432 : Integer.Sparse Key := [(key1853, -2), (key1857, -2), (key1853, -2), (key1857, 6), (key1853, -2), (key1857, -2), (key1853, -2), (key1885, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1885, 2), (key1888, -2), (key1857, -2), (key1888, -2), (key1857, 6), (key1888, -2), (key1857, -2), (key1888, -2)]

def rawRow17433 : Integer.Sparse Key := [(key1857, -2), (key1853, -2), (key1853, -2), (key1857, 6), (key1857, -2), (key1853, -2), (key1853, -2), (key1888, 2), (key1885, 2), (key1888, 2), (key1853, 2), (key1885, 2), (key1853, 2), (key1888, -2), (key1888, -2), (key1857, -2), (key1857, 6), (key1888, -2), (key1888, -2), (key1857, -2)]

def rawRow17434 : Integer.Sparse Key := [(key1853, -2), (key1857, -2), (key1857, -2), (key1853, 6), (key1885, -2), (key1888, -2), (key1888, -2), (key1853, 2), (key1857, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1888, 2), (key1853, -2), (key1853, -2), (key1885, -2), (key1888, 6), (key1857, -2), (key1857, -2), (key1888, -2)]

def rawRow17435 : Integer.Sparse Key := [(key1857, -2), (key1853, -2), (key1857, -2), (key1853, 6), (key1888, -2), (key1885, -2), (key1888, -2), (key1857, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1853, -2), (key1885, -2), (key1853, -2), (key1888, 6), (key1857, -2), (key1888, -2), (key1857, -2)]

def rawRow17436 : Integer.Sparse Key := [(key1857, -2), (key1857, -2), (key1853, -2), (key1853, 6), (key1888, -2), (key1888, -2), (key1885, -2), (key1888, 2), (key1888, 2), (key1857, 2), (key1857, 2), (key1853, 2), (key1853, 2), (key1885, -2), (key1853, -2), (key1853, -2), (key1888, 6), (key1888, -2), (key1857, -2), (key1857, -2)]

def rawRow17437 : Integer.Sparse Key := [(key1885, -2), (key1888, -2), (key1888, -2), (key1888, 6), (key1853, -2), (key1857, -2), (key1857, -2), (key1853, 2), (key1857, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1888, 2), (key1857, -2), (key1857, -2), (key1888, -2), (key1853, 6), (key1853, -2), (key1853, -2), (key1885, -2)]

def rawRow17438 : Integer.Sparse Key := [(key1888, -2), (key1885, -2), (key1888, -2), (key1888, 6), (key1857, -2), (key1853, -2), (key1857, -2), (key1857, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1857, -2), (key1888, -2), (key1857, -2), (key1853, 6), (key1853, -2), (key1885, -2), (key1853, -2)]

def rawRow17439 : Integer.Sparse Key := [(key1888, -2), (key1888, -2), (key1885, -2), (key1888, 6), (key1857, -2), (key1857, -2), (key1853, -2), (key1888, 2), (key1888, 2), (key1857, 2), (key1857, 2), (key1853, 2), (key1853, 2), (key1888, -2), (key1857, -2), (key1857, -2), (key1853, 6), (key1885, -2), (key1853, -2), (key1853, -2)]

def rawRow17440 : Integer.Sparse Key := [(key1888, -2), (key1888, -2), (key1888, -2), (key1885, 6), (key1888, -2), (key1888, -2), (key1888, -2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1853, -2), (key1853, -2), (key1853, -2), (key1885, 6), (key1853, -2), (key1853, -2), (key1853, -2)]

def rawRow17441 : Integer.Sparse Key := [(key1959, 6), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, 6), (key1959, -2), (key1967, -2), (key1967, -2), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1961, 2), (key1961, 2), (key1967, 2), (key1967, 2), (key1970, 2), (key1970, 2)]

def rawRow17442 : Integer.Sparse Key := [(key1959, 6), (key1961, -2), (key1959, -2), (key1961, -2), (key1959, 6), (key1967, -2), (key1959, -2), (key1967, -2), (key1961, -2), (key1959, -2), (key1961, -2), (key1967, -2), (key1959, -2), (key1967, -2), (key1967, 2), (key1970, 2), (key1961, 2), (key1970, 2), (key1961, 2), (key1967, 2)]

def rawRow17443 : Integer.Sparse Key := [(key1959, 6), (key1961, -2), (key1961, -2), (key1959, -2), (key1959, 6), (key1967, -2), (key1967, -2), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1959, -2), (key1970, 2), (key1967, 2), (key1970, 2), (key1961, 2), (key1967, 2), (key1961, 2)]

def rawRow17444 : Integer.Sparse Key := [(key1961, 6), (key1959, -2), (key1959, -2), (key1961, -2), (key1967, 6), (key1959, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, -2), (key1961, -2), (key1970, -2), (key1959, 2), (key1961, 2), (key1959, 2), (key1967, 2), (key1961, 2), (key1967, 2)]

def rawRow17445 : Integer.Sparse Key := [(key1961, 6), (key1959, -2), (key1961, -2), (key1959, -2), (key1967, 6), (key1959, -2), (key1967, -2), (key1959, -2), (key1967, -2), (key1970, -2), (key1967, -2), (key1961, -2), (key1970, -2), (key1961, -2), (key1961, 2), (key1959, 2), (key1967, 2), (key1959, 2), (key1967, 2), (key1961, 2)]

def rawRow17446 : Integer.Sparse Key := [(key1961, 6), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, 6), (key1967, -2), (key1959, -2), (key1959, -2), (key1970, -2), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, -2), (key1961, -2), (key1967, 2), (key1967, 2), (key1961, 2), (key1961, 2), (key1959, 2), (key1959, 2)]

def rawRow17447 : Integer.Sparse Key := [(key1967, 6), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, 6), (key1961, -2), (key1961, -2), (key1970, -2), (key1959, -2), (key1959, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, 2), (key1961, 2), (key1959, 2), (key1967, 2), (key1961, 2), (key1967, 2)]

def rawRow17448 : Integer.Sparse Key := [(key1967, 6), (key1967, -2), (key1970, -2), (key1967, -2), (key1961, 6), (key1961, -2), (key1970, -2), (key1961, -2), (key1959, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, -2), (key1961, 2), (key1959, 2), (key1967, 2), (key1959, 2), (key1967, 2), (key1961, 2)]

def rawRow17449 : Integer.Sparse Key := [(key1967, 6), (key1970, -2), (key1967, -2), (key1967, -2), (key1961, 6), (key1970, -2), (key1961, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, -2), (key1959, -2), (key1967, 2), (key1967, 2), (key1961, 2), (key1961, 2), (key1959, 2), (key1959, 2)]

def rawRow17450 : Integer.Sparse Key := [(key1970, 6), (key1967, -2), (key1967, -2), (key1967, -2), (key1970, 6), (key1961, -2), (key1961, -2), (key1961, -2), (key1967, -2), (key1967, -2), (key1967, -2), (key1961, -2), (key1961, -2), (key1961, -2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2)]

def rawRow17451 : Integer.Sparse Key := [(key665, -2), (key665, -2), (key666, -2), (key666, 6), (key665, -2), (key665, -2), (key666, -2), (key665, 2), (key665, 2), (key682, 2), (key682, 2), (key683, 2), (key683, 2), (key666, -2), (key683, -2), (key683, -2), (key666, 6), (key666, -2), (key683, -2), (key683, -2)]

def rawRow17452 : Integer.Sparse Key := [(key665, -2), (key666, -2), (key665, -2), (key666, 6), (key665, -2), (key666, -2), (key665, -2), (key682, 2), (key683, 2), (key665, 2), (key683, 2), (key665, 2), (key682, 2), (key683, -2), (key666, -2), (key683, -2), (key666, 6), (key683, -2), (key666, -2), (key683, -2)]

def rawRow17453 : Integer.Sparse Key := [(key666, -2), (key665, -2), (key665, -2), (key666, 6), (key666, -2), (key665, -2), (key665, -2), (key683, 2), (key682, 2), (key683, 2), (key665, 2), (key682, 2), (key665, 2), (key683, -2), (key683, -2), (key666, -2), (key666, 6), (key683, -2), (key683, -2), (key666, -2)]

def rawRow17454 : Integer.Sparse Key := [(key665, -2), (key666, -2), (key666, -2), (key665, 6), (key682, -2), (key683, -2), (key683, -2), (key665, 2), (key666, 2), (key665, 2), (key683, 2), (key666, 2), (key683, 2), (key665, -2), (key665, -2), (key682, -2), (key683, 6), (key666, -2), (key666, -2), (key683, -2)]

def rawRow17455 : Integer.Sparse Key := [(key666, -2), (key665, -2), (key666, -2), (key665, 6), (key683, -2), (key682, -2), (key683, -2), (key666, 2), (key665, 2), (key683, 2), (key665, 2), (key683, 2), (key666, 2), (key665, -2), (key682, -2), (key665, -2), (key683, 6), (key666, -2), (key683, -2), (key666, -2)]

def rawRow17456 : Integer.Sparse Key := [(key666, -2), (key666, -2), (key665, -2), (key665, 6), (key683, -2), (key683, -2), (key682, -2), (key683, 2), (key683, 2), (key666, 2), (key666, 2), (key665, 2), (key665, 2), (key682, -2), (key665, -2), (key665, -2), (key683, 6), (key683, -2), (key666, -2), (key666, -2)]

def rawRow17457 : Integer.Sparse Key := [(key682, -2), (key683, -2), (key683, -2), (key683, 6), (key665, -2), (key666, -2), (key666, -2), (key665, 2), (key666, 2), (key665, 2), (key683, 2), (key666, 2), (key683, 2), (key666, -2), (key666, -2), (key683, -2), (key665, 6), (key665, -2), (key665, -2), (key682, -2)]

def rawRow17458 : Integer.Sparse Key := [(key683, -2), (key682, -2), (key683, -2), (key683, 6), (key666, -2), (key665, -2), (key666, -2), (key666, 2), (key665, 2), (key683, 2), (key665, 2), (key683, 2), (key666, 2), (key666, -2), (key683, -2), (key666, -2), (key665, 6), (key665, -2), (key682, -2), (key665, -2)]

def rawRow17459 : Integer.Sparse Key := [(key683, -2), (key683, -2), (key682, -2), (key683, 6), (key666, -2), (key666, -2), (key665, -2), (key683, 2), (key683, 2), (key666, 2), (key666, 2), (key665, 2), (key665, 2), (key683, -2), (key666, -2), (key666, -2), (key665, 6), (key682, -2), (key665, -2), (key665, -2)]

def rawRow17460 : Integer.Sparse Key := [(key683, -2), (key683, -2), (key683, -2), (key682, 6), (key683, -2), (key683, -2), (key683, -2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key665, -2), (key665, -2), (key665, -2), (key682, 6), (key665, -2), (key665, -2), (key665, -2)]

def rawRow17461 : Integer.Sparse Key := [(key621, 4), (key649, 4), (key649, 4), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key653, -2), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key653, -2), (key625, 4), (key653, 4), (key653, 4)]

def rawRow17462 : Integer.Sparse Key := [(key649, 4), (key621, 4), (key649, 4), (key649, -2), (key653, -2), (key623, -2), (key653, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key623, -2), (key653, -2), (key623, -2), (key649, -2), (key653, 4), (key625, 4), (key653, 4)]

def rawRow17463 : Integer.Sparse Key := [(key649, 4), (key649, 4), (key621, 4), (key653, -2), (key649, -2), (key653, -2), (key623, -2), (key649, -2), (key623, -2), (key653, -2), (key649, -2), (key653, -2), (key623, -2), (key649, -2), (key623, -2), (key653, 4), (key653, 4), (key625, 4)]

def rawRow17464 : Integer.Sparse Key := [(key623, 4), (key623, 4), (key653, 4), (key621, -2), (key623, -2), (key621, -2), (key649, -2), (key623, -2), (key649, -2), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key625, -2), (key653, -2), (key623, 4), (key623, 4), (key649, 4)]

def rawRow17465 : Integer.Sparse Key := [(key623, 4), (key653, 4), (key623, 4), (key623, -2), (key621, -2), (key649, -2), (key621, -2), (key649, -2), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key623, -2), (key653, -2), (key625, -2), (key623, 4), (key649, 4), (key623, 4)]

def rawRow17466 : Integer.Sparse Key := [(key653, 4), (key623, 4), (key623, 4), (key649, -2), (key649, -2), (key623, -2), (key623, -2), (key621, -2), (key621, -2), (key653, -2), (key653, -2), (key625, -2), (key625, -2), (key623, -2), (key623, -2), (key649, 4), (key623, 4), (key623, 4)]

def rawRow17467 : Integer.Sparse Key := [(key623, 4), (key623, 4), (key653, 4), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key625, -2), (key653, -2), (key621, -2), (key623, -2), (key621, -2), (key649, -2), (key623, -2), (key649, -2), (key623, 4), (key623, 4), (key649, 4)]

def rawRow17468 : Integer.Sparse Key := [(key623, 4), (key653, 4), (key623, 4), (key625, -2), (key623, -2), (key653, -2), (key623, -2), (key653, -2), (key625, -2), (key623, -2), (key621, -2), (key649, -2), (key621, -2), (key649, -2), (key623, -2), (key623, 4), (key649, 4), (key623, 4)]

def rawRow17469 : Integer.Sparse Key := [(key653, 4), (key623, 4), (key623, 4), (key653, -2), (key653, -2), (key625, -2), (key625, -2), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key623, -2), (key623, -2), (key621, -2), (key621, -2), (key649, 4), (key623, 4), (key623, 4)]

def rawRow17470 : Integer.Sparse Key := [(key625, 4), (key625, 4), (key625, 4), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key621, 4), (key621, 4), (key621, 4)]

def rawRow17471 : Integer.Sparse Key := [(key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1866, 2), (key1881, 2), (key1881, 2), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1868, 2), (key1868, 2), (key1878, 2), (key1878, 2), (key1889, 2), (key1889, 2), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1889, -1), (key1889, -1), (key1866, 2), (key1881, 2), (key1881, 2), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1889, -1), (key1889, -1)]

def rawRow17472 : Integer.Sparse Key := [(key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1881, 2), (key1866, 2), (key1881, 2), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1878, 2), (key1889, 2), (key1868, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1881, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1881, 2), (key1866, 2), (key1881, 2), (key1881, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, -1), (key1881, -1)]

def rawRow17473 : Integer.Sparse Key := [(key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1866, 2), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1889, 2), (key1878, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1868, 2), (key1889, -1), (key1881, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1871, -1), (key1881, 2), (key1881, 2), (key1866, 2), (key1889, -1), (key1881, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1871, -1)]

def rawRow17474 : Integer.Sparse Key := [(key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1), (key1871, 2), (key1871, 2), (key1889, 2), (key1866, -1), (key1871, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1881, -1)]

def rawRow17475 : Integer.Sparse Key := [(key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1871, 2), (key1889, 2), (key1871, 2), (key1871, -1), (key1866, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1871, -1)]

def rawRow17476 : Integer.Sparse Key := [(key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1), (key1889, 2), (key1871, 2), (key1871, 2), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1)]

def rawRow17477 : Integer.Sparse Key := [(key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, 2), (key1871, 2), (key1889, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2), (key1866, -1), (key1871, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1881, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1)]

def rawRow17478 : Integer.Sparse Key := [(key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1889, 2), (key1871, 2), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1871, -1), (key1866, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1)]

def rawRow17479 : Integer.Sparse Key := [(key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1889, 2), (key1871, 2), (key1871, 2), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1)]

def rawRow17480 : Integer.Sparse Key := [(key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1)]

def rawRow17481 : Integer.Sparse Key := [(key1963, 4), (key1965, 4), (key1965, 4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1968, 12)]

def rawRow17482 : Integer.Sparse Key := [(key1965, 4), (key1963, 4), (key1965, 4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1968, 12)]

def rawRow17483 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1963, 4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, 12)]

def rawRow17484 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1968, 4), (key1963, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1968, -4), (key1965, 12)]

def rawRow17485 : Integer.Sparse Key := [(key1965, 4), (key1968, 4), (key1965, 4), (key1965, -4), (key1963, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1968, -4), (key1965, 12)]

def rawRow17486 : Integer.Sparse Key := [(key1968, 4), (key1965, 4), (key1965, 4), (key1965, -4), (key1965, -4), (key1963, -4), (key1968, -4), (key1968, -4), (key1965, -4), (key1965, 12)]

def rawRow17487 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1968, 4), (key1965, -4), (key1968, -4), (key1968, -4), (key1963, -4), (key1965, -4), (key1965, -4), (key1965, 12)]

def rawRow17488 : Integer.Sparse Key := [(key1965, 4), (key1968, 4), (key1965, 4), (key1968, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1963, -4), (key1965, -4), (key1965, 12)]

def rawRow17489 : Integer.Sparse Key := [(key1968, 4), (key1965, 4), (key1965, 4), (key1968, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1963, -4), (key1965, 12)]

def rawRow17490 : Integer.Sparse Key := [(key1968, 4), (key1968, 4), (key1968, 4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1963, 12)]

def rawRow17491 : Integer.Sparse Key := [(key1934, -2), (key1934, -2), (key1935, -2), (key1935, 6), (key1934, -2), (key1934, -2), (key1935, -2), (key1934, 2), (key1934, 2), (key1954, 2), (key1954, 2), (key1955, 2), (key1955, 2), (key1935, -2), (key1955, -2), (key1955, -2), (key1935, 6), (key1935, -2), (key1955, -2), (key1955, -2)]

def rawRow17492 : Integer.Sparse Key := [(key1934, -2), (key1935, -2), (key1934, -2), (key1935, 6), (key1934, -2), (key1935, -2), (key1934, -2), (key1954, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1954, 2), (key1955, -2), (key1935, -2), (key1955, -2), (key1935, 6), (key1955, -2), (key1935, -2), (key1955, -2)]

def rawRow17493 : Integer.Sparse Key := [(key1935, -2), (key1934, -2), (key1934, -2), (key1935, 6), (key1935, -2), (key1934, -2), (key1934, -2), (key1955, 2), (key1954, 2), (key1955, 2), (key1934, 2), (key1954, 2), (key1934, 2), (key1955, -2), (key1955, -2), (key1935, -2), (key1935, 6), (key1955, -2), (key1955, -2), (key1935, -2)]

def rawRow17494 : Integer.Sparse Key := [(key1934, -2), (key1935, -2), (key1935, -2), (key1934, 6), (key1954, -2), (key1955, -2), (key1955, -2), (key1934, 2), (key1935, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1955, 2), (key1934, -2), (key1934, -2), (key1954, -2), (key1955, 6), (key1935, -2), (key1935, -2), (key1955, -2)]

def rawRow17495 : Integer.Sparse Key := [(key1935, -2), (key1934, -2), (key1935, -2), (key1934, 6), (key1955, -2), (key1954, -2), (key1955, -2), (key1935, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1934, -2), (key1954, -2), (key1934, -2), (key1955, 6), (key1935, -2), (key1955, -2), (key1935, -2)]

def rawRow17496 : Integer.Sparse Key := [(key1935, -2), (key1935, -2), (key1934, -2), (key1934, 6), (key1955, -2), (key1955, -2), (key1954, -2), (key1955, 2), (key1955, 2), (key1935, 2), (key1935, 2), (key1934, 2), (key1934, 2), (key1954, -2), (key1934, -2), (key1934, -2), (key1955, 6), (key1955, -2), (key1935, -2), (key1935, -2)]

def rawRow17497 : Integer.Sparse Key := [(key1954, -2), (key1955, -2), (key1955, -2), (key1955, 6), (key1934, -2), (key1935, -2), (key1935, -2), (key1934, 2), (key1935, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1955, 2), (key1935, -2), (key1935, -2), (key1955, -2), (key1934, 6), (key1934, -2), (key1934, -2), (key1954, -2)]

def rawRow17498 : Integer.Sparse Key := [(key1955, -2), (key1954, -2), (key1955, -2), (key1955, 6), (key1935, -2), (key1934, -2), (key1935, -2), (key1935, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1935, -2), (key1955, -2), (key1935, -2), (key1934, 6), (key1934, -2), (key1954, -2), (key1934, -2)]

def rawRow17499 : Integer.Sparse Key := [(key1955, -2), (key1955, -2), (key1954, -2), (key1955, 6), (key1935, -2), (key1935, -2), (key1934, -2), (key1955, 2), (key1955, 2), (key1935, 2), (key1935, 2), (key1934, 2), (key1934, 2), (key1955, -2), (key1935, -2), (key1935, -2), (key1934, 6), (key1954, -2), (key1934, -2), (key1934, -2)]

def rawRow17500 : Integer.Sparse Key := [(key1955, -2), (key1955, -2), (key1955, -2), (key1954, 6), (key1955, -2), (key1955, -2), (key1955, -2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1934, -2), (key1934, -2), (key1934, -2), (key1954, 6), (key1934, -2), (key1934, -2), (key1934, -2)]

def rawRow17501 : Integer.Sparse Key := [(key688, 4), (key689, 4), (key689, 4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key691, 12)]

def rawRow17502 : Integer.Sparse Key := [(key689, 4), (key688, 4), (key689, 4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key691, 12)]

def rawRow17503 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key688, 4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, 12)]

def rawRow17504 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key691, 4), (key688, -4), (key689, -4), (key689, -4), (key689, -4), (key691, -4), (key691, -4), (key689, 12)]

def rawRow17505 : Integer.Sparse Key := [(key689, 4), (key691, 4), (key689, 4), (key689, -4), (key688, -4), (key689, -4), (key691, -4), (key689, -4), (key691, -4), (key689, 12)]

def rawRow17506 : Integer.Sparse Key := [(key691, 4), (key689, 4), (key689, 4), (key689, -4), (key689, -4), (key688, -4), (key691, -4), (key691, -4), (key689, -4), (key689, 12)]

def rawRow17507 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key691, 4), (key689, -4), (key691, -4), (key691, -4), (key688, -4), (key689, -4), (key689, -4), (key689, 12)]

def rawRow17508 : Integer.Sparse Key := [(key689, 4), (key691, 4), (key689, 4), (key691, -4), (key689, -4), (key691, -4), (key689, -4), (key688, -4), (key689, -4), (key689, 12)]

def rawRow17509 : Integer.Sparse Key := [(key691, 4), (key689, 4), (key689, 4), (key691, -4), (key691, -4), (key689, -4), (key689, -4), (key689, -4), (key688, -4), (key689, 12)]

def rawRow17510 : Integer.Sparse Key := [(key691, 4), (key691, 4), (key691, 4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key688, 12)]

def rawRow17511 : Integer.Sparse Key := [(key1938, -1), (key1938, -1), (key1950, -1), (key1950, -1), (key1951, -1), (key1951, -1), (key1939, 2), (key1951, 2), (key1951, 2), (key1938, -1), (key1938, -1), (key1950, -1), (key1950, -1), (key1951, -1), (key1951, -1), (key1941, 2), (key1941, 2), (key1950, 2), (key1950, 2), (key1956, 2), (key1956, 2), (key1942, -1), (key1942, -1), (key1951, -1), (key1951, -1), (key1956, -1), (key1956, -1), (key1939, 2), (key1951, 2), (key1951, 2), (key1942, -1), (key1942, -1), (key1951, -1), (key1951, -1), (key1956, -1), (key1956, -1)]

def rawRow17512 : Integer.Sparse Key := [(key1950, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1951, 2), (key1939, 2), (key1951, 2), (key1950, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1950, 2), (key1956, 2), (key1941, 2), (key1956, 2), (key1941, 2), (key1950, 2), (key1951, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1951, 2), (key1939, 2), (key1951, 2), (key1951, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, -1), (key1951, -1)]

def rawRow17513 : Integer.Sparse Key := [(key1951, -1), (key1950, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1951, 2), (key1951, 2), (key1939, 2), (key1951, -1), (key1950, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1956, 2), (key1950, 2), (key1956, 2), (key1941, 2), (key1950, 2), (key1941, 2), (key1956, -1), (key1951, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1942, -1), (key1951, 2), (key1951, 2), (key1939, 2), (key1956, -1), (key1951, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1942, -1)]

def rawRow17514 : Integer.Sparse Key := [(key1938, -1), (key1939, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1941, -1), (key1942, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1938, 2), (key1942, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1951, 2), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1), (key1942, 2), (key1942, 2), (key1956, 2), (key1939, -1), (key1942, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1951, -1)]

def rawRow17515 : Integer.Sparse Key := [(key1939, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1942, -1), (key1941, -1), (key1956, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1942, 2), (key1938, 2), (key1951, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1942, 2), (key1956, 2), (key1942, 2), (key1942, -1), (key1939, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1942, -1)]

def rawRow17516 : Integer.Sparse Key := [(key1951, -1), (key1951, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1956, -1), (key1956, -1), (key1942, -1), (key1942, -1), (key1941, -1), (key1941, -1), (key1951, 2), (key1951, 2), (key1942, 2), (key1942, 2), (key1938, 2), (key1938, 2), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1), (key1956, 2), (key1942, 2), (key1942, 2), (key1951, -1), (key1951, -1), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1)]

def rawRow17517 : Integer.Sparse Key := [(key1941, -1), (key1942, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, 2), (key1942, 2), (key1956, 2), (key1938, -1), (key1939, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1938, 2), (key1942, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1951, 2), (key1939, -1), (key1942, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1951, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1)]

def rawRow17518 : Integer.Sparse Key := [(key1942, -1), (key1941, -1), (key1956, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1942, 2), (key1956, 2), (key1942, 2), (key1939, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1942, 2), (key1938, 2), (key1951, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1942, -1), (key1939, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1)]

def rawRow17519 : Integer.Sparse Key := [(key1956, -1), (key1956, -1), (key1942, -1), (key1942, -1), (key1941, -1), (key1941, -1), (key1956, 2), (key1942, 2), (key1942, 2), (key1951, -1), (key1951, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1951, 2), (key1951, 2), (key1942, 2), (key1942, 2), (key1938, 2), (key1938, 2), (key1951, -1), (key1951, -1), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1)]

def rawRow17520 : Integer.Sparse Key := [(key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1)]

def rawRow17521 : Integer.Sparse Key := [(key517, -2), (key517, -2), (key524, -2), (key524, 6), (key517, -2), (key517, -2), (key524, -2), (key517, 2), (key517, 2), (key549, 2), (key549, 2), (key555, 2), (key555, 2), (key524, -2), (key555, -2), (key555, -2), (key524, 6), (key524, -2), (key555, -2), (key555, -2)]

def rawRow17522 : Integer.Sparse Key := [(key517, -2), (key524, -2), (key517, -2), (key524, 6), (key517, -2), (key524, -2), (key517, -2), (key549, 2), (key555, 2), (key517, 2), (key555, 2), (key517, 2), (key549, 2), (key555, -2), (key524, -2), (key555, -2), (key524, 6), (key555, -2), (key524, -2), (key555, -2)]

def rawRow17523 : Integer.Sparse Key := [(key524, -2), (key517, -2), (key517, -2), (key524, 6), (key524, -2), (key517, -2), (key517, -2), (key555, 2), (key549, 2), (key555, 2), (key517, 2), (key549, 2), (key517, 2), (key555, -2), (key555, -2), (key524, -2), (key524, 6), (key555, -2), (key555, -2), (key524, -2)]

def rawRow17524 : Integer.Sparse Key := [(key517, -2), (key524, -2), (key524, -2), (key517, 6), (key549, -2), (key555, -2), (key555, -2), (key517, 2), (key524, 2), (key517, 2), (key555, 2), (key524, 2), (key555, 2), (key517, -2), (key517, -2), (key549, -2), (key555, 6), (key524, -2), (key524, -2), (key555, -2)]

def rawRow17525 : Integer.Sparse Key := [(key524, -2), (key517, -2), (key524, -2), (key517, 6), (key555, -2), (key549, -2), (key555, -2), (key524, 2), (key517, 2), (key555, 2), (key517, 2), (key555, 2), (key524, 2), (key517, -2), (key549, -2), (key517, -2), (key555, 6), (key524, -2), (key555, -2), (key524, -2)]

def rawRow17526 : Integer.Sparse Key := [(key524, -2), (key524, -2), (key517, -2), (key517, 6), (key555, -2), (key555, -2), (key549, -2), (key555, 2), (key555, 2), (key524, 2), (key524, 2), (key517, 2), (key517, 2), (key549, -2), (key517, -2), (key517, -2), (key555, 6), (key555, -2), (key524, -2), (key524, -2)]

def rawRow17527 : Integer.Sparse Key := [(key549, -2), (key555, -2), (key555, -2), (key555, 6), (key517, -2), (key524, -2), (key524, -2), (key517, 2), (key524, 2), (key517, 2), (key555, 2), (key524, 2), (key555, 2), (key524, -2), (key524, -2), (key555, -2), (key517, 6), (key517, -2), (key517, -2), (key549, -2)]

def rawRow17528 : Integer.Sparse Key := [(key555, -2), (key549, -2), (key555, -2), (key555, 6), (key524, -2), (key517, -2), (key524, -2), (key524, 2), (key517, 2), (key555, 2), (key517, 2), (key555, 2), (key524, 2), (key524, -2), (key555, -2), (key524, -2), (key517, 6), (key517, -2), (key549, -2), (key517, -2)]

def rawRow17529 : Integer.Sparse Key := [(key555, -2), (key555, -2), (key549, -2), (key555, 6), (key524, -2), (key524, -2), (key517, -2), (key555, 2), (key555, 2), (key524, 2), (key524, 2), (key517, 2), (key517, 2), (key555, -2), (key524, -2), (key524, -2), (key517, 6), (key549, -2), (key517, -2), (key517, -2)]

def rawRow17530 : Integer.Sparse Key := [(key555, -2), (key555, -2), (key555, -2), (key549, 6), (key555, -2), (key555, -2), (key555, -2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key517, -2), (key517, -2), (key517, -2), (key549, 6), (key517, -2), (key517, -2), (key517, -2)]

def rawRow17531 : Integer.Sparse Key := [(key1854, 2), (key1856, 2), (key1856, 2), (key1856, -2), (key1856, -2), (key1858, -2), (key1854, 2), (key1856, 2), (key1856, 2), (key1856, -1), (key1856, -1), (key1887, -1), (key1887, -1), (key1890, -1), (key1890, -1), (key1856, -2), (key1856, -2), (key1858, -2), (key1856, -1), (key1856, -1), (key1887, -1), (key1887, -1), (key1890, -1), (key1890, -1), (key1858, 4), (key1890, 4), (key1890, 4)]

def rawRow17532 : Integer.Sparse Key := [(key1856, 2), (key1854, 2), (key1856, 2), (key1856, -2), (key1858, -2), (key1856, -2), (key1856, 2), (key1854, 2), (key1856, 2), (key1887, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -2), (key1858, -2), (key1856, -2), (key1887, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1890, 4), (key1858, 4), (key1890, 4)]

def rawRow17533 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1854, 2), (key1858, -2), (key1856, -2), (key1856, -2), (key1856, 2), (key1856, 2), (key1854, 2), (key1890, -1), (key1887, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -1), (key1858, -2), (key1856, -2), (key1856, -2), (key1890, -1), (key1887, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -1), (key1890, 4), (key1890, 4), (key1858, 4)]

def rawRow17534 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1858, 2), (key1854, -2), (key1856, -2), (key1856, -2), (key1887, 2), (key1887, 2), (key1890, 2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, -1), (key1858, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1890, -1), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17535 : Integer.Sparse Key := [(key1856, 2), (key1858, 2), (key1856, 2), (key1856, -2), (key1854, -2), (key1856, -2), (key1887, 2), (key1890, 2), (key1887, 2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1890, -2), (key1887, -2), (key1890, -2), (key1858, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1856, 4), (key1887, 4), (key1856, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17536 : Integer.Sparse Key := [(key1858, 2), (key1856, 2), (key1856, 2), (key1856, -2), (key1856, -2), (key1854, -2), (key1890, 2), (key1887, 2), (key1887, 2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1890, -2), (key1890, -2), (key1887, -2), (key1890, -1), (key1890, -1), (key1858, -1), (key1858, -1), (key1856, -1), (key1856, -1), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17537 : Integer.Sparse Key := [(key1887, 2), (key1887, 2), (key1890, 2), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, 2), (key1856, 2), (key1858, 2), (key1856, -1), (key1858, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1890, -1), (key1854, -2), (key1856, -2), (key1856, -2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1856, 4), (key1856, 4), (key1887, 4)]

def rawRow17538 : Integer.Sparse Key := [(key1887, 2), (key1890, 2), (key1887, 2), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, 2), (key1858, 2), (key1856, 2), (key1858, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1856, -2), (key1854, -2), (key1856, -2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1856, 4), (key1887, 4), (key1856, 4)]

def rawRow17539 : Integer.Sparse Key := [(key1890, 2), (key1887, 2), (key1887, 2), (key1890, -2), (key1890, -2), (key1887, -2), (key1858, 2), (key1856, 2), (key1856, 2), (key1890, -1), (key1890, -1), (key1858, -1), (key1858, -1), (key1856, -1), (key1856, -1), (key1856, -2), (key1856, -2), (key1854, -2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1887, 4), (key1856, 4), (key1856, 4)]

def rawRow17540 : Integer.Sparse Key := [(key1890, 2), (key1890, 2), (key1890, 2), (key1887, -2), (key1887, -2), (key1887, -2), (key1890, 2), (key1890, 2), (key1890, 2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1887, -2), (key1887, -2), (key1887, -2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1854, 4), (key1854, 4), (key1854, 4)]

def rawRow17541 : Integer.Sparse Key := [(key1862, 2), (key1862, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, 2), (key1862, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1868, 2), (key1868, 2), (key1878, 2), (key1878, 2), (key1889, 2), (key1889, 2)]

def rawRow17542 : Integer.Sparse Key := [(key1862, 2), (key1866, 2), (key1862, 2), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, 2), (key1866, 2), (key1862, 2), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1878, 2), (key1889, 2), (key1868, 2), (key1889, 2), (key1868, 2), (key1878, 2)]

def rawRow17543 : Integer.Sparse Key := [(key1866, 2), (key1862, 2), (key1862, 2), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1866, 2), (key1862, 2), (key1862, 2), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1889, 2), (key1878, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1868, 2)]

def rawRow17544 : Integer.Sparse Key := [(key1868, 2), (key1871, 2), (key1871, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1878, 2), (key1881, 2), (key1881, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2)]

def rawRow17545 : Integer.Sparse Key := [(key1871, 2), (key1868, 2), (key1871, 2), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1881, 2), (key1878, 2), (key1881, 2), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2)]

def rawRow17546 : Integer.Sparse Key := [(key1871, 2), (key1871, 2), (key1868, 2), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1878, 2), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2)]

def rawRow17547 : Integer.Sparse Key := [(key1878, 2), (key1881, 2), (key1881, 2), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, 2), (key1871, 2), (key1871, 2), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2)]

def rawRow17548 : Integer.Sparse Key := [(key1881, 2), (key1878, 2), (key1881, 2), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, 2), (key1868, 2), (key1871, 2), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2)]

def rawRow17549 : Integer.Sparse Key := [(key1881, 2), (key1881, 2), (key1878, 2), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1871, 2), (key1871, 2), (key1868, 2), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2)]

def rawRow17550 : Integer.Sparse Key := [(key1889, 2), (key1889, 2), (key1889, 2), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1889, 2), (key1889, 2), (key1889, 2), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2)]

def rawRow17551 : Integer.Sparse Key := [(key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1871, 2), (key1871, 2), (key1862, 1), (key1862, 1), (key1878, 1), (key1878, 1), (key1881, 1), (key1881, 1), (key1866, -2), (key1881, -2), (key1881, -2), (key1862, -1), (key1862, -1), (key1868, -1), (key1868, -1), (key1871, -1), (key1871, -1), (key1862, 1), (key1862, 1), (key1878, 1), (key1878, 1), (key1881, 1), (key1881, 1), (key1866, 2), (key1871, 2), (key1871, 2), (key1866, -2), (key1881, -2), (key1881, -2)]

def rawRow17552 : Integer.Sparse Key := [(key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1871, 2), (key1866, 2), (key1871, 2), (key1878, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1881, -2), (key1866, -2), (key1881, -2), (key1868, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1878, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1871, 2), (key1866, 2), (key1871, 2), (key1881, -2), (key1866, -2), (key1881, -2)]

def rawRow17553 : Integer.Sparse Key := [(key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1871, 2), (key1871, 2), (key1866, 2), (key1881, 1), (key1878, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1881, -2), (key1881, -2), (key1866, -2), (key1871, -1), (key1868, -1), (key1871, -1), (key1862, -1), (key1868, -1), (key1862, -1), (key1881, 1), (key1878, 1), (key1881, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1871, 2), (key1871, 2), (key1866, 2), (key1881, -2), (key1881, -2), (key1866, -2)]

def rawRow17554 : Integer.Sparse Key := [(key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, 2), (key1862, 2), (key1868, 2), (key1862, 1), (key1866, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1862, -2), (key1862, -2), (key1878, -2), (key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1868, 1), (key1871, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1881, 2), (key1881, 2), (key1889, 2), (key1871, -2), (key1871, -2), (key1889, -2)]

def rawRow17555 : Integer.Sparse Key := [(key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1862, 2), (key1868, 2), (key1862, 2), (key1866, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1862, -2), (key1878, -2), (key1862, -2), (key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1871, 1), (key1868, 1), (key1889, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1881, 2), (key1889, 2), (key1881, 2), (key1871, -2), (key1889, -2), (key1871, -2)]

def rawRow17556 : Integer.Sparse Key := [(key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1868, 2), (key1862, 2), (key1862, 2), (key1881, 1), (key1881, 1), (key1866, 1), (key1866, 1), (key1862, 1), (key1862, 1), (key1878, -2), (key1862, -2), (key1862, -2), (key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, 1), (key1889, 1), (key1871, 1), (key1871, 1), (key1868, 1), (key1868, 1), (key1889, 2), (key1881, 2), (key1881, 2), (key1889, -2), (key1871, -2), (key1871, -2)]

def rawRow17557 : Integer.Sparse Key := [(key1878, -1), (key1881, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1889, -1), (key1881, 2), (key1881, 2), (key1889, 2), (key1868, 1), (key1871, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, -2), (key1871, -2), (key1889, -2), (key1862, -1), (key1866, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1871, -1), (key1862, 1), (key1866, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1881, 1), (key1862, 2), (key1862, 2), (key1868, 2), (key1862, -2), (key1862, -2), (key1878, -2)]

def rawRow17558 : Integer.Sparse Key := [(key1881, -1), (key1878, -1), (key1889, -1), (key1878, -1), (key1889, -1), (key1881, -1), (key1881, 2), (key1889, 2), (key1881, 2), (key1871, 1), (key1868, 1), (key1889, 1), (key1868, 1), (key1889, 1), (key1871, 1), (key1871, -2), (key1889, -2), (key1871, -2), (key1866, -1), (key1862, -1), (key1871, -1), (key1862, -1), (key1871, -1), (key1866, -1), (key1866, 1), (key1862, 1), (key1881, 1), (key1862, 1), (key1881, 1), (key1866, 1), (key1862, 2), (key1868, 2), (key1862, 2), (key1862, -2), (key1878, -2), (key1862, -2)]

def rawRow17559 : Integer.Sparse Key := [(key1889, -1), (key1889, -1), (key1881, -1), (key1881, -1), (key1878, -1), (key1878, -1), (key1889, 2), (key1881, 2), (key1881, 2), (key1889, 1), (key1889, 1), (key1871, 1), (key1871, 1), (key1868, 1), (key1868, 1), (key1889, -2), (key1871, -2), (key1871, -2), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 1), (key1881, 1), (key1866, 1), (key1866, 1), (key1862, 1), (key1862, 1), (key1868, 2), (key1862, 2), (key1862, 2), (key1878, -2), (key1862, -2), (key1862, -2)]

def rawRow17560 : Integer.Sparse Key := [(key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1878, 2), (key1878, 2), (key1878, 2), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1868, -2), (key1868, -2), (key1868, -2), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1881, -1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1871, 1), (key1878, 2), (key1878, 2), (key1878, 2), (key1868, -2), (key1868, -2), (key1868, -2)]

def rawRow17561 : Integer.Sparse Key := [(key1938, -1), (key1938, -1), (key1941, -1), (key1941, -1), (key1942, -1), (key1942, -1), (key1939, 2), (key1942, 2), (key1942, 2), (key1938, 1), (key1938, 1), (key1950, 1), (key1950, 1), (key1951, 1), (key1951, 1), (key1939, -2), (key1951, -2), (key1951, -2), (key1938, -1), (key1938, -1), (key1941, -1), (key1941, -1), (key1942, -1), (key1942, -1), (key1938, 1), (key1938, 1), (key1950, 1), (key1950, 1), (key1951, 1), (key1951, 1), (key1939, 2), (key1942, 2), (key1942, 2), (key1939, -2), (key1951, -2), (key1951, -2)]

def rawRow17562 : Integer.Sparse Key := [(key1941, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1942, 2), (key1939, 2), (key1942, 2), (key1950, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1951, -2), (key1939, -2), (key1951, -2), (key1941, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1950, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1942, 2), (key1939, 2), (key1942, 2), (key1951, -2), (key1939, -2), (key1951, -2)]

def rawRow17563 : Integer.Sparse Key := [(key1942, -1), (key1941, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1938, -1), (key1942, 2), (key1942, 2), (key1939, 2), (key1951, 1), (key1950, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1951, -2), (key1951, -2), (key1939, -2), (key1942, -1), (key1941, -1), (key1942, -1), (key1938, -1), (key1941, -1), (key1938, -1), (key1951, 1), (key1950, 1), (key1951, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1942, 2), (key1942, 2), (key1939, 2), (key1951, -2), (key1951, -2), (key1939, -2)]

def rawRow17564 : Integer.Sparse Key := [(key1938, -1), (key1939, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1942, -1), (key1938, 2), (key1938, 2), (key1941, 2), (key1938, 1), (key1939, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1938, -2), (key1938, -2), (key1950, -2), (key1950, -1), (key1951, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1956, -1), (key1941, 1), (key1942, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1951, 2), (key1951, 2), (key1956, 2), (key1942, -2), (key1942, -2), (key1956, -2)]

def rawRow17565 : Integer.Sparse Key := [(key1939, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1938, 2), (key1941, 2), (key1938, 2), (key1939, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1938, -2), (key1950, -2), (key1938, -2), (key1951, -1), (key1950, -1), (key1956, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1942, 1), (key1941, 1), (key1956, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1951, 2), (key1956, 2), (key1951, 2), (key1942, -2), (key1956, -2), (key1942, -2)]

def rawRow17566 : Integer.Sparse Key := [(key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1941, 2), (key1938, 2), (key1938, 2), (key1951, 1), (key1951, 1), (key1939, 1), (key1939, 1), (key1938, 1), (key1938, 1), (key1950, -2), (key1938, -2), (key1938, -2), (key1956, -1), (key1956, -1), (key1951, -1), (key1951, -1), (key1950, -1), (key1950, -1), (key1956, 1), (key1956, 1), (key1942, 1), (key1942, 1), (key1941, 1), (key1941, 1), (key1956, 2), (key1951, 2), (key1951, 2), (key1956, -2), (key1942, -2), (key1942, -2)]

def rawRow17567 : Integer.Sparse Key := [(key1950, -1), (key1951, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1956, -1), (key1951, 2), (key1951, 2), (key1956, 2), (key1941, 1), (key1942, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1956, 1), (key1942, -2), (key1942, -2), (key1956, -2), (key1938, -1), (key1939, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1942, -1), (key1938, 1), (key1939, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1951, 1), (key1938, 2), (key1938, 2), (key1941, 2), (key1938, -2), (key1938, -2), (key1950, -2)]

def rawRow17568 : Integer.Sparse Key := [(key1951, -1), (key1950, -1), (key1956, -1), (key1950, -1), (key1956, -1), (key1951, -1), (key1951, 2), (key1956, 2), (key1951, 2), (key1942, 1), (key1941, 1), (key1956, 1), (key1941, 1), (key1956, 1), (key1942, 1), (key1942, -2), (key1956, -2), (key1942, -2), (key1939, -1), (key1938, -1), (key1942, -1), (key1938, -1), (key1942, -1), (key1939, -1), (key1939, 1), (key1938, 1), (key1951, 1), (key1938, 1), (key1951, 1), (key1939, 1), (key1938, 2), (key1941, 2), (key1938, 2), (key1938, -2), (key1950, -2), (key1938, -2)]

def rawRow17569 : Integer.Sparse Key := [(key1956, -1), (key1956, -1), (key1951, -1), (key1951, -1), (key1950, -1), (key1950, -1), (key1956, 2), (key1951, 2), (key1951, 2), (key1956, 1), (key1956, 1), (key1942, 1), (key1942, 1), (key1941, 1), (key1941, 1), (key1956, -2), (key1942, -2), (key1942, -2), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1951, 1), (key1951, 1), (key1939, 1), (key1939, 1), (key1938, 1), (key1938, 1), (key1941, 2), (key1938, 2), (key1938, 2), (key1950, -2), (key1938, -2), (key1938, -2)]

def rawRow17570 : Integer.Sparse Key := [(key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1950, 2), (key1950, 2), (key1950, 2), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1941, -2), (key1941, -2), (key1941, -2), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1951, -1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1942, 1), (key1950, 2), (key1950, 2), (key1950, 2), (key1941, -2), (key1941, -2), (key1941, -2)]

def rawRow17571 : Integer.Sparse Key := [(key1863, 2), (key1880, 2), (key1880, 2), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1883, -1), (key1863, 2), (key1880, 2), (key1880, 2), (key1870, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1891, -1), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1883, -1), (key1870, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1891, -1), (key1872, 2), (key1872, 2), (key1883, 2), (key1883, 2), (key1891, 2), (key1891, 2)]

def rawRow17572 : Integer.Sparse Key := [(key1880, 2), (key1863, 2), (key1880, 2), (key1880, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1880, 2), (key1863, 2), (key1880, 2), (key1880, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1883, 2), (key1891, 2), (key1872, 2), (key1891, 2), (key1872, 2), (key1883, 2)]

def rawRow17573 : Integer.Sparse Key := [(key1880, 2), (key1880, 2), (key1863, 2), (key1883, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1865, -1), (key1880, 2), (key1880, 2), (key1863, 2), (key1891, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1883, -1), (key1880, -1), (key1883, -1), (key1865, -1), (key1880, -1), (key1865, -1), (key1891, -1), (key1880, -1), (key1891, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1891, 2), (key1883, 2), (key1891, 2), (key1872, 2), (key1883, 2), (key1872, 2)]

def rawRow17574 : Integer.Sparse Key := [(key1865, 2), (key1865, 2), (key1883, 2), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1870, 2), (key1870, 2), (key1891, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1891, -1), (key1865, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1883, -1), (key1865, 2), (key1870, 2), (key1865, 2), (key1880, 2), (key1870, 2), (key1880, 2)]

def rawRow17575 : Integer.Sparse Key := [(key1865, 2), (key1883, 2), (key1865, 2), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, 2), (key1891, 2), (key1870, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1870, 2), (key1865, 2), (key1880, 2), (key1865, 2), (key1880, 2), (key1870, 2)]

def rawRow17576 : Integer.Sparse Key := [(key1883, 2), (key1865, 2), (key1865, 2), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1891, 2), (key1870, 2), (key1870, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1891, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1870, -1), (key1870, -1), (key1883, -1), (key1883, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1865, -1), (key1880, 2), (key1880, 2), (key1870, 2), (key1870, 2), (key1865, 2), (key1865, 2)]

def rawRow17577 : Integer.Sparse Key := [(key1870, 2), (key1870, 2), (key1891, 2), (key1870, -1), (key1872, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1891, -1), (key1865, 2), (key1865, 2), (key1883, 2), (key1865, -1), (key1872, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1883, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1865, 2), (key1870, 2), (key1865, 2), (key1880, 2), (key1870, 2), (key1880, 2)]

def rawRow17578 : Integer.Sparse Key := [(key1870, 2), (key1891, 2), (key1870, 2), (key1872, -1), (key1870, -1), (key1891, -1), (key1870, -1), (key1891, -1), (key1872, -1), (key1865, 2), (key1883, 2), (key1865, 2), (key1872, -1), (key1865, -1), (key1883, -1), (key1865, -1), (key1883, -1), (key1872, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1870, 2), (key1865, 2), (key1880, 2), (key1865, 2), (key1880, 2), (key1870, 2)]

def rawRow17579 : Integer.Sparse Key := [(key1891, 2), (key1870, 2), (key1870, 2), (key1891, -1), (key1891, -1), (key1872, -1), (key1872, -1), (key1870, -1), (key1870, -1), (key1883, 2), (key1865, 2), (key1865, 2), (key1883, -1), (key1883, -1), (key1872, -1), (key1872, -1), (key1865, -1), (key1865, -1), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1880, 2), (key1880, 2), (key1870, 2), (key1870, 2), (key1865, 2), (key1865, 2)]

def rawRow17580 : Integer.Sparse Key := [(key1872, 2), (key1872, 2), (key1872, 2), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1872, 2), (key1872, 2), (key1872, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2), (key1863, 2)]

def rawRow17581 : Integer.Sparse Key := [(key533, 4), (key533, 4), (key536, 4), (key533, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key533, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key539, 4), (key539, 4), (key556, 4)]

def rawRow17582 : Integer.Sparse Key := [(key533, 4), (key536, 4), (key533, 4), (key539, -2), (key544, -2), (key533, -2), (key544, -2), (key533, -2), (key539, -2), (key539, -2), (key544, -2), (key533, -2), (key544, -2), (key533, -2), (key539, -2), (key539, 4), (key556, 4), (key539, 4)]

def rawRow17583 : Integer.Sparse Key := [(key536, 4), (key533, 4), (key533, 4), (key544, -2), (key539, -2), (key544, -2), (key533, -2), (key539, -2), (key533, -2), (key544, -2), (key539, -2), (key544, -2), (key533, -2), (key539, -2), (key533, -2), (key556, 4), (key539, 4), (key539, 4)]

def rawRow17584 : Integer.Sparse Key := [(key539, 4), (key544, 4), (key544, 4), (key533, -2), (key536, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key539, -2), (key544, -2), (key539, -2), (key556, -2), (key544, -2), (key556, -2), (key533, 4), (key544, 4), (key544, 4)]

def rawRow17585 : Integer.Sparse Key := [(key544, 4), (key539, 4), (key544, 4), (key536, -2), (key533, -2), (key544, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key539, -2), (key556, -2), (key539, -2), (key556, -2), (key544, -2), (key544, 4), (key533, 4), (key544, 4)]

def rawRow17586 : Integer.Sparse Key := [(key544, 4), (key544, 4), (key539, 4), (key544, -2), (key544, -2), (key536, -2), (key536, -2), (key533, -2), (key533, -2), (key556, -2), (key556, -2), (key544, -2), (key544, -2), (key539, -2), (key539, -2), (key544, 4), (key544, 4), (key533, 4)]

def rawRow17587 : Integer.Sparse Key := [(key539, 4), (key544, 4), (key544, 4), (key539, -2), (key544, -2), (key539, -2), (key556, -2), (key544, -2), (key556, -2), (key533, -2), (key536, -2), (key533, -2), (key544, -2), (key536, -2), (key544, -2), (key533, 4), (key544, 4), (key544, 4)]

def rawRow17588 : Integer.Sparse Key := [(key544, 4), (key539, 4), (key544, 4), (key544, -2), (key539, -2), (key556, -2), (key539, -2), (key556, -2), (key544, -2), (key536, -2), (key533, -2), (key544, -2), (key533, -2), (key544, -2), (key536, -2), (key544, 4), (key533, 4), (key544, 4)]

def rawRow17589 : Integer.Sparse Key := [(key544, 4), (key544, 4), (key539, 4), (key556, -2), (key556, -2), (key544, -2), (key544, -2), (key539, -2), (key539, -2), (key544, -2), (key544, -2), (key536, -2), (key536, -2), (key533, -2), (key533, -2), (key544, 4), (key544, 4), (key533, 4)]

def rawRow17590 : Integer.Sparse Key := [(key556, 4), (key556, 4), (key556, 4), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key544, -2), (key536, 4), (key536, 4), (key536, 4)]

def rawRow17591 : Integer.Sparse Key := [(key633, -2), (key633, -2), (key635, -2), (key635, -2), (key638, -2), (key638, -2), (key635, 2), (key635, 2), (key644, 2), (key638, 2), (key638, 2), (key644, 2), (key635, 2), (key635, 2), (key644, 2), (key644, -6), (key638, 2), (key638, 2), (key644, 2), (key644, -6)]

def rawRow17592 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key633, -2), (key638, -2), (key633, -2), (key635, -2), (key635, 2), (key644, 2), (key635, 2), (key638, 2), (key644, 2), (key638, 2), (key635, 2), (key644, 2), (key635, 2), (key644, -6), (key638, 2), (key644, 2), (key638, 2), (key644, -6)]

def rawRow17593 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key638, -2), (key633, -2), (key635, -2), (key633, -2), (key644, 2), (key635, 2), (key635, 2), (key644, 2), (key638, 2), (key638, 2), (key644, 2), (key635, 2), (key635, 2), (key644, -6), (key644, 2), (key638, 2), (key638, 2), (key644, -6)]

def rawRow17594 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key635, -2), (key644, -2), (key638, -2), (key644, -2), (key633, 2), (key638, 2), (key638, 2), (key633, 2), (key635, 2), (key635, 2), (key635, 2), (key644, 2), (key644, 2), (key635, -6), (key638, 2), (key644, 2), (key644, 2), (key638, -6)]

def rawRow17595 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key644, -2), (key635, -2), (key644, -2), (key638, -2), (key638, 2), (key633, 2), (key638, 2), (key635, 2), (key633, 2), (key635, 2), (key644, 2), (key635, 2), (key644, 2), (key635, -6), (key644, 2), (key638, 2), (key644, 2), (key638, -6)]

def rawRow17596 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key638, -2), (key638, -2), (key635, -2), (key635, -2), (key638, 2), (key638, 2), (key633, 2), (key635, 2), (key635, 2), (key633, 2), (key644, 2), (key644, 2), (key635, 2), (key635, -6), (key644, 2), (key644, 2), (key638, 2), (key638, -6)]

def rawRow17597 : Integer.Sparse Key := [(key635, -2), (key638, -2), (key635, -2), (key644, -2), (key638, -2), (key644, -2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key644, 2), (key644, 2), (key633, 2), (key638, 2), (key638, 2), (key638, -6), (key633, 2), (key635, 2), (key635, 2), (key635, -6)]

def rawRow17598 : Integer.Sparse Key := [(key638, -2), (key635, -2), (key644, -2), (key635, -2), (key644, -2), (key638, -2), (key644, 2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key644, 2), (key638, 2), (key633, 2), (key638, 2), (key638, -6), (key635, 2), (key633, 2), (key635, 2), (key635, -6)]

def rawRow17599 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key638, -2), (key638, -2), (key635, -2), (key635, -2), (key644, 2), (key644, 2), (key635, 2), (key644, 2), (key644, 2), (key638, 2), (key638, 2), (key638, 2), (key633, 2), (key638, -6), (key635, 2), (key635, 2), (key633, 2), (key635, -6)]

def rawRow17600 : Integer.Sparse Key := [(key644, -2), (key644, -2), (key644, -2), (key644, -2), (key644, -2), (key644, -2), (key638, 2), (key638, 2), (key638, 2), (key635, 2), (key635, 2), (key635, 2), (key638, 2), (key638, 2), (key638, 2), (key633, -6), (key635, 2), (key635, 2), (key635, 2), (key633, -6)]

def rawRow17601 : Integer.Sparse Key := [(key291, 4), (key294, 4), (key294, 4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key298, 12)]

def rawRow17602 : Integer.Sparse Key := [(key294, 4), (key291, 4), (key294, 4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key298, 12)]

def rawRow17603 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key291, 4), (key298, -4), (key294, -4), (key294, -4), (key298, -4), (key294, -4), (key294, -4), (key298, 12)]

def rawRow17604 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key298, 4), (key291, -4), (key294, -4), (key294, -4), (key294, -4), (key298, -4), (key298, -4), (key294, 12)]

def rawRow17605 : Integer.Sparse Key := [(key294, 4), (key298, 4), (key294, 4), (key294, -4), (key291, -4), (key294, -4), (key298, -4), (key294, -4), (key298, -4), (key294, 12)]

def rawRow17606 : Integer.Sparse Key := [(key298, 4), (key294, 4), (key294, 4), (key294, -4), (key294, -4), (key291, -4), (key298, -4), (key298, -4), (key294, -4), (key294, 12)]

def rawRow17607 : Integer.Sparse Key := [(key294, 4), (key294, 4), (key298, 4), (key294, -4), (key298, -4), (key298, -4), (key291, -4), (key294, -4), (key294, -4), (key294, 12)]

def rawRow17608 : Integer.Sparse Key := [(key294, 4), (key298, 4), (key294, 4), (key298, -4), (key294, -4), (key298, -4), (key294, -4), (key291, -4), (key294, -4), (key294, 12)]

def rawRow17609 : Integer.Sparse Key := [(key298, 4), (key294, 4), (key294, 4), (key298, -4), (key298, -4), (key294, -4), (key294, -4), (key294, -4), (key291, -4), (key294, 12)]

def rawRow17610 : Integer.Sparse Key := [(key298, 4), (key298, 4), (key298, 4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key294, -4), (key291, 12)]

def rawRow17611 : Integer.Sparse Key := [(key2237, 4), (key2237, 4), (key2260, 4), (key2271, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2295, -2), (key2271, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2295, -2), (key2325, 4), (key2325, 4), (key2337, 4)]

def rawRow17612 : Integer.Sparse Key := [(key2237, 4), (key2260, 4), (key2237, 4), (key2273, -2), (key2271, -2), (key2295, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2295, -2), (key2271, -2), (key2295, -2), (key2273, -2), (key2325, 4), (key2337, 4), (key2325, 4)]

def rawRow17613 : Integer.Sparse Key := [(key2260, 4), (key2237, 4), (key2237, 4), (key2295, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2271, -2), (key2295, -2), (key2295, -2), (key2273, -2), (key2273, -2), (key2271, -2), (key2271, -2), (key2337, 4), (key2325, 4), (key2325, 4)]

def rawRow17614 : Integer.Sparse Key := [(key1992, 4), (key2271, 4), (key2295, 4), (key1992, -2), (key1995, -2), (key2237, -2), (key2260, -2), (key2273, -2), (key2295, -2), (key2002, -2), (key2004, -2), (key2271, -2), (key2295, -2), (key2325, -2), (key2337, -2), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17615 : Integer.Sparse Key := [(key1992, 4), (key2295, 4), (key2271, 4), (key1995, -2), (key1992, -2), (key2260, -2), (key2237, -2), (key2295, -2), (key2273, -2), (key2004, -2), (key2002, -2), (key2295, -2), (key2271, -2), (key2337, -2), (key2325, -2), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17616 : Integer.Sparse Key := [(key2271, 4), (key1992, 4), (key2295, 4), (key2237, -2), (key2273, -2), (key1992, -2), (key2295, -2), (key1995, -2), (key2260, -2), (key2271, -2), (key2325, -2), (key2002, -2), (key2337, -2), (key2004, -2), (key2295, -2), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17617 : Integer.Sparse Key := [(key2271, 4), (key2295, 4), (key1992, 4), (key2273, -2), (key2237, -2), (key2295, -2), (key1992, -2), (key2260, -2), (key1995, -2), (key2325, -2), (key2271, -2), (key2337, -2), (key2002, -2), (key2295, -2), (key2004, -2), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17618 : Integer.Sparse Key := [(key2295, 4), (key1992, 4), (key2271, 4), (key2260, -2), (key2295, -2), (key1995, -2), (key2273, -2), (key1992, -2), (key2237, -2), (key2295, -2), (key2337, -2), (key2004, -2), (key2325, -2), (key2002, -2), (key2271, -2), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17619 : Integer.Sparse Key := [(key2295, 4), (key2271, 4), (key1992, 4), (key2295, -2), (key2260, -2), (key2273, -2), (key1995, -2), (key2237, -2), (key1992, -2), (key2337, -2), (key2295, -2), (key2325, -2), (key2004, -2), (key2271, -2), (key2002, -2), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17620 : Integer.Sparse Key := [(key1992, 4), (key2271, 4), (key2295, 4), (key2002, -2), (key2004, -2), (key2271, -2), (key2295, -2), (key2325, -2), (key2337, -2), (key1992, -2), (key1995, -2), (key2237, -2), (key2260, -2), (key2273, -2), (key2295, -2), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17621 : Integer.Sparse Key := [(key1992, 4), (key2295, 4), (key2271, 4), (key2004, -2), (key2002, -2), (key2295, -2), (key2271, -2), (key2337, -2), (key2325, -2), (key1995, -2), (key1992, -2), (key2260, -2), (key2237, -2), (key2295, -2), (key2273, -2), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17622 : Integer.Sparse Key := [(key2271, 4), (key1992, 4), (key2295, 4), (key2271, -2), (key2325, -2), (key2002, -2), (key2337, -2), (key2004, -2), (key2295, -2), (key2237, -2), (key2273, -2), (key1992, -2), (key2295, -2), (key1995, -2), (key2260, -2), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17623 : Integer.Sparse Key := [(key2271, 4), (key2295, 4), (key1992, 4), (key2325, -2), (key2271, -2), (key2337, -2), (key2002, -2), (key2295, -2), (key2004, -2), (key2273, -2), (key2237, -2), (key2295, -2), (key1992, -2), (key2260, -2), (key1995, -2), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17624 : Integer.Sparse Key := [(key2295, 4), (key1992, 4), (key2271, 4), (key2295, -2), (key2337, -2), (key2004, -2), (key2325, -2), (key2002, -2), (key2271, -2), (key2260, -2), (key2295, -2), (key1995, -2), (key2273, -2), (key1992, -2), (key2237, -2), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17625 : Integer.Sparse Key := [(key2295, 4), (key2271, 4), (key1992, 4), (key2337, -2), (key2295, -2), (key2325, -2), (key2004, -2), (key2271, -2), (key2002, -2), (key2295, -2), (key2260, -2), (key2273, -2), (key1995, -2), (key2237, -2), (key1992, -2), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17626 : Integer.Sparse Key := [(key2002, 4), (key2002, 4), (key2337, 4), (key1992, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2295, -2), (key1992, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2295, -2), (key1995, 4), (key1995, 4), (key2260, 4)]

def rawRow17627 : Integer.Sparse Key := [(key2002, 4), (key2337, 4), (key2002, 4), (key2004, -2), (key1992, -2), (key2295, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key2295, -2), (key1992, -2), (key2295, -2), (key2004, -2), (key1995, 4), (key2260, 4), (key1995, 4)]

def rawRow17628 : Integer.Sparse Key := [(key2337, 4), (key2002, 4), (key2002, 4), (key2295, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key1992, -2), (key2295, -2), (key2295, -2), (key2004, -2), (key2004, -2), (key1992, -2), (key1992, -2), (key2260, 4), (key1995, 4), (key1995, 4)]

def rawRow17629 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key62, -2), (key72, 6), (key704, -2), (key709, -2), (key709, -2), (key858, 2), (key863, 2), (key858, 2), (key885, 2), (key863, 2), (key885, 2), (key923, -2), (key923, -2), (key940, -2), (key723, 6), (key923, -2), (key923, -2), (key940, -2)]

def rawRow17630 : Integer.Sparse Key := [(key62, -2), (key60, -2), (key62, -2), (key72, 6), (key709, -2), (key704, -2), (key709, -2), (key863, 2), (key858, 2), (key885, 2), (key858, 2), (key885, 2), (key863, 2), (key923, -2), (key940, -2), (key923, -2), (key723, 6), (key923, -2), (key940, -2), (key923, -2)]

def rawRow17631 : Integer.Sparse Key := [(key62, -2), (key62, -2), (key60, -2), (key72, 6), (key709, -2), (key709, -2), (key704, -2), (key885, 2), (key885, 2), (key863, 2), (key863, 2), (key858, 2), (key858, 2), (key940, -2), (key923, -2), (key923, -2), (key723, 6), (key940, -2), (key923, -2), (key923, -2)]

def rawRow17632 : Integer.Sparse Key := [(key60, -2), (key62, -2), (key72, -2), (key62, 6), (key858, -2), (key863, -2), (key923, -2), (key704, 2), (key709, 2), (key858, 2), (key885, 2), (key923, 2), (key940, 2), (key709, -2), (key863, -2), (key885, -2), (key923, 6), (key723, -2), (key923, -2), (key940, -2)]

def rawRow17633 : Integer.Sparse Key := [(key62, -2), (key60, -2), (key72, -2), (key62, 6), (key863, -2), (key858, -2), (key923, -2), (key709, 2), (key704, 2), (key885, 2), (key858, 2), (key940, 2), (key923, 2), (key709, -2), (key885, -2), (key863, -2), (key923, 6), (key723, -2), (key940, -2), (key923, -2)]

def rawRow17634 : Integer.Sparse Key := [(key60, -2), (key72, -2), (key62, -2), (key62, 6), (key858, -2), (key923, -2), (key863, -2), (key858, 2), (key923, 2), (key704, 2), (key940, 2), (key709, 2), (key885, 2), (key863, -2), (key709, -2), (key885, -2), (key923, 6), (key923, -2), (key723, -2), (key940, -2)]

def rawRow17635 : Integer.Sparse Key := [(key72, -2), (key60, -2), (key62, -2), (key62, 6), (key923, -2), (key858, -2), (key863, -2), (key923, 2), (key858, 2), (key940, 2), (key704, 2), (key885, 2), (key709, 2), (key863, -2), (key885, -2), (key709, -2), (key923, 6), (key923, -2), (key940, -2), (key723, -2)]

def rawRow17636 : Integer.Sparse Key := [(key62, -2), (key72, -2), (key60, -2), (key62, 6), (key863, -2), (key923, -2), (key858, -2), (key885, 2), (key940, 2), (key709, 2), (key923, 2), (key704, 2), (key858, 2), (key885, -2), (key709, -2), (key863, -2), (key923, 6), (key940, -2), (key723, -2), (key923, -2)]

def rawRow17637 : Integer.Sparse Key := [(key72, -2), (key62, -2), (key60, -2), (key62, 6), (key923, -2), (key863, -2), (key858, -2), (key940, 2), (key885, 2), (key923, 2), (key709, 2), (key858, 2), (key704, 2), (key885, -2), (key863, -2), (key709, -2), (key923, 6), (key940, -2), (key923, -2), (key723, -2)]

def rawRow17638 : Integer.Sparse Key := [(key125, -2), (key127, -2), (key135, -2), (key135, 6), (key60, -2), (key62, -2), (key72, -2), (key704, 2), (key709, 2), (key858, 2), (key885, 2), (key923, 2), (key940, 2), (key723, -2), (key923, -2), (key940, -2), (key709, 6), (key709, -2), (key863, -2), (key885, -2)]

def rawRow17639 : Integer.Sparse Key := [(key127, -2), (key125, -2), (key135, -2), (key135, 6), (key62, -2), (key60, -2), (key72, -2), (key709, 2), (key704, 2), (key885, 2), (key858, 2), (key940, 2), (key923, 2), (key723, -2), (key940, -2), (key923, -2), (key709, 6), (key709, -2), (key885, -2), (key863, -2)]

def rawRow17640 : Integer.Sparse Key := [(key125, -2), (key135, -2), (key127, -2), (key135, 6), (key60, -2), (key72, -2), (key62, -2), (key858, 2), (key923, 2), (key704, 2), (key940, 2), (key709, 2), (key885, 2), (key923, -2), (key723, -2), (key940, -2), (key709, 6), (key863, -2), (key709, -2), (key885, -2)]

def rawRow17641 : Integer.Sparse Key := [(key135, -2), (key125, -2), (key127, -2), (key135, 6), (key72, -2), (key60, -2), (key62, -2), (key923, 2), (key858, 2), (key940, 2), (key704, 2), (key885, 2), (key709, 2), (key923, -2), (key940, -2), (key723, -2), (key709, 6), (key863, -2), (key885, -2), (key709, -2)]

def rawRow17642 : Integer.Sparse Key := [(key127, -2), (key135, -2), (key125, -2), (key135, 6), (key62, -2), (key72, -2), (key60, -2), (key885, 2), (key940, 2), (key709, 2), (key923, 2), (key704, 2), (key858, 2), (key940, -2), (key723, -2), (key923, -2), (key709, 6), (key885, -2), (key709, -2), (key863, -2)]

def rawRow17643 : Integer.Sparse Key := [(key135, -2), (key127, -2), (key125, -2), (key135, 6), (key72, -2), (key62, -2), (key60, -2), (key940, 2), (key885, 2), (key923, 2), (key709, 2), (key858, 2), (key704, 2), (key940, -2), (key923, -2), (key723, -2), (key709, 6), (key885, -2), (key863, -2), (key709, -2)]

def rawRow17644 : Integer.Sparse Key := [(key125, -2), (key135, -2), (key135, -2), (key127, 6), (key125, -2), (key135, -2), (key135, -2), (key60, 2), (key72, 2), (key704, 2), (key940, 2), (key723, 2), (key940, 2), (key709, -2), (key709, -2), (key885, -2), (key863, 6), (key709, -2), (key709, -2), (key885, -2)]

def rawRow17645 : Integer.Sparse Key := [(key135, -2), (key125, -2), (key135, -2), (key127, 6), (key135, -2), (key125, -2), (key135, -2), (key72, 2), (key60, 2), (key940, 2), (key704, 2), (key940, 2), (key723, 2), (key709, -2), (key885, -2), (key709, -2), (key863, 6), (key709, -2), (key885, -2), (key709, -2)]

def rawRow17646 : Integer.Sparse Key := [(key135, -2), (key135, -2), (key125, -2), (key127, 6), (key135, -2), (key135, -2), (key125, -2), (key180, 2), (key180, 2), (key72, 2), (key72, 2), (key704, 2), (key704, 2), (key885, -2), (key709, -2), (key709, -2), (key863, 6), (key885, -2), (key709, -2), (key709, -2)]

def rawRow17647 : Integer.Sparse Key := [(key1988, -2), (key1993, -2), (key1993, -2), (key2008, 6), (key1988, -2), (key1993, -2), (key1993, -2), (key2233, 2), (key2238, 2), (key2233, 2), (key2258, 2), (key2238, 2), (key2258, 2), (key2301, -2), (key2301, -2), (key2314, -2), (key2008, 6), (key2301, -2), (key2301, -2), (key2314, -2)]

def rawRow17648 : Integer.Sparse Key := [(key1993, -2), (key1988, -2), (key1993, -2), (key2008, 6), (key1993, -2), (key1988, -2), (key1993, -2), (key2238, 2), (key2233, 2), (key2258, 2), (key2233, 2), (key2258, 2), (key2238, 2), (key2301, -2), (key2314, -2), (key2301, -2), (key2008, 6), (key2301, -2), (key2314, -2), (key2301, -2)]

def rawRow17649 : Integer.Sparse Key := [(key1993, -2), (key1993, -2), (key1988, -2), (key2008, 6), (key1993, -2), (key1993, -2), (key1988, -2), (key2258, 2), (key2258, 2), (key2238, 2), (key2238, 2), (key2233, 2), (key2233, 2), (key2314, -2), (key2301, -2), (key2301, -2), (key2008, 6), (key2314, -2), (key2301, -2), (key2301, -2)]

def rawRow17650 : Integer.Sparse Key := [(key1988, -2), (key1993, -2), (key2008, -2), (key1993, 6), (key2233, -2), (key2238, -2), (key2301, -2), (key1988, 2), (key1993, 2), (key2233, 2), (key2258, 2), (key2301, 2), (key2314, 2), (key1993, -2), (key2238, -2), (key2258, -2), (key2301, 6), (key2008, -2), (key2301, -2), (key2314, -2)]

def rawRow17651 : Integer.Sparse Key := [(key1993, -2), (key1988, -2), (key2008, -2), (key1993, 6), (key2238, -2), (key2233, -2), (key2301, -2), (key1993, 2), (key1988, 2), (key2258, 2), (key2233, 2), (key2314, 2), (key2301, 2), (key1993, -2), (key2258, -2), (key2238, -2), (key2301, 6), (key2008, -2), (key2314, -2), (key2301, -2)]

def rawRow17652 : Integer.Sparse Key := [(key1988, -2), (key2008, -2), (key1993, -2), (key1993, 6), (key2233, -2), (key2301, -2), (key2238, -2), (key2233, 2), (key2301, 2), (key1988, 2), (key2314, 2), (key1993, 2), (key2258, 2), (key2238, -2), (key1993, -2), (key2258, -2), (key2301, 6), (key2301, -2), (key2008, -2), (key2314, -2)]

def rawRow17653 : Integer.Sparse Key := [(key2008, -2), (key1988, -2), (key1993, -2), (key1993, 6), (key2301, -2), (key2233, -2), (key2238, -2), (key2301, 2), (key2233, 2), (key2314, 2), (key1988, 2), (key2258, 2), (key1993, 2), (key2238, -2), (key2258, -2), (key1993, -2), (key2301, 6), (key2301, -2), (key2314, -2), (key2008, -2)]

def rawRow17654 : Integer.Sparse Key := [(key1993, -2), (key2008, -2), (key1988, -2), (key1993, 6), (key2238, -2), (key2301, -2), (key2233, -2), (key2258, 2), (key2314, 2), (key1993, 2), (key2301, 2), (key1988, 2), (key2233, 2), (key2258, -2), (key1993, -2), (key2238, -2), (key2301, 6), (key2314, -2), (key2008, -2), (key2301, -2)]

def rawRow17655 : Integer.Sparse Key := [(key2008, -2), (key1993, -2), (key1988, -2), (key1993, 6), (key2301, -2), (key2238, -2), (key2233, -2), (key2314, 2), (key2258, 2), (key2301, 2), (key1993, 2), (key2233, 2), (key1988, 2), (key2258, -2), (key2238, -2), (key1993, -2), (key2301, 6), (key2314, -2), (key2301, -2), (key2008, -2)]

def rawRow17656 : Integer.Sparse Key := [(key2233, -2), (key2238, -2), (key2301, -2), (key2301, 6), (key1988, -2), (key1993, -2), (key2008, -2), (key1988, 2), (key1993, 2), (key2233, 2), (key2258, 2), (key2301, 2), (key2314, 2), (key2008, -2), (key2301, -2), (key2314, -2), (key1993, 6), (key1993, -2), (key2238, -2), (key2258, -2)]

def rawRow17657 : Integer.Sparse Key := [(key2238, -2), (key2233, -2), (key2301, -2), (key2301, 6), (key1993, -2), (key1988, -2), (key2008, -2), (key1993, 2), (key1988, 2), (key2258, 2), (key2233, 2), (key2314, 2), (key2301, 2), (key2008, -2), (key2314, -2), (key2301, -2), (key1993, 6), (key1993, -2), (key2258, -2), (key2238, -2)]

def rawRow17658 : Integer.Sparse Key := [(key2233, -2), (key2301, -2), (key2238, -2), (key2301, 6), (key1988, -2), (key2008, -2), (key1993, -2), (key2233, 2), (key2301, 2), (key1988, 2), (key2314, 2), (key1993, 2), (key2258, 2), (key2301, -2), (key2008, -2), (key2314, -2), (key1993, 6), (key2238, -2), (key1993, -2), (key2258, -2)]

def rawRow17659 : Integer.Sparse Key := [(key2301, -2), (key2233, -2), (key2238, -2), (key2301, 6), (key2008, -2), (key1988, -2), (key1993, -2), (key2301, 2), (key2233, 2), (key2314, 2), (key1988, 2), (key2258, 2), (key1993, 2), (key2301, -2), (key2314, -2), (key2008, -2), (key1993, 6), (key2238, -2), (key2258, -2), (key1993, -2)]

def rawRow17660 : Integer.Sparse Key := [(key2238, -2), (key2301, -2), (key2233, -2), (key2301, 6), (key1993, -2), (key2008, -2), (key1988, -2), (key2258, 2), (key2314, 2), (key1993, 2), (key2301, 2), (key1988, 2), (key2233, 2), (key2314, -2), (key2008, -2), (key2301, -2), (key1993, 6), (key2258, -2), (key1993, -2), (key2238, -2)]

def rawRow17661 : Integer.Sparse Key := [(key2301, -2), (key2238, -2), (key2233, -2), (key2301, 6), (key2008, -2), (key1993, -2), (key1988, -2), (key2314, 2), (key2258, 2), (key2301, 2), (key1993, 2), (key2233, 2), (key1988, 2), (key2314, -2), (key2301, -2), (key2008, -2), (key1993, 6), (key2258, -2), (key2238, -2), (key1993, -2)]

def rawRow17662 : Integer.Sparse Key := [(key2233, -2), (key2301, -2), (key2301, -2), (key2238, 6), (key2233, -2), (key2301, -2), (key2301, -2), (key1988, 2), (key2008, 2), (key1988, 2), (key2314, 2), (key2008, 2), (key2314, 2), (key1993, -2), (key1993, -2), (key2258, -2), (key2238, 6), (key1993, -2), (key1993, -2), (key2258, -2)]

def rawRow17663 : Integer.Sparse Key := [(key2301, -2), (key2233, -2), (key2301, -2), (key2238, 6), (key2301, -2), (key2233, -2), (key2301, -2), (key2008, 2), (key1988, 2), (key2314, 2), (key1988, 2), (key2314, 2), (key2008, 2), (key1993, -2), (key2258, -2), (key1993, -2), (key2238, 6), (key1993, -2), (key2258, -2), (key1993, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17664 : Integer.Sparse Key := [(key2301, -2), (key2301, -2), (key2233, -2), (key2238, 6), (key2301, -2), (key2301, -2), (key2233, -2), (key2314, 2), (key2314, 2), (key2008, 2), (key2008, 2), (key1988, 2), (key1988, 2), (key2258, -2), (key1993, -2), (key1993, -2), (key2238, 6), (key2258, -2), (key1993, -2), (key1993, -2)]

def rawRow17665 : Integer.Sparse Key := [(key2030, 6), (key2060, -2), (key2060, -2), (key2068, -2), (key2030, 6), (key2149, -2), (key2149, -2), (key2165, -2), (key2060, -2), (key2060, -2), (key2068, -2), (key2149, -2), (key2149, -2), (key2165, -2), (key2242, 2), (key2245, 2), (key2242, 2), (key2252, 2), (key2245, 2), (key2252, 2)]

def rawRow17666 : Integer.Sparse Key := [(key2030, 6), (key2060, -2), (key2068, -2), (key2060, -2), (key2030, 6), (key2149, -2), (key2165, -2), (key2149, -2), (key2060, -2), (key2068, -2), (key2060, -2), (key2149, -2), (key2165, -2), (key2149, -2), (key2245, 2), (key2242, 2), (key2252, 2), (key2242, 2), (key2252, 2), (key2245, 2)]

def rawRow17667 : Integer.Sparse Key := [(key2030, 6), (key2068, -2), (key2060, -2), (key2060, -2), (key2030, 6), (key2165, -2), (key2149, -2), (key2149, -2), (key2068, -2), (key2060, -2), (key2060, -2), (key2165, -2), (key2149, -2), (key2149, -2), (key2252, 2), (key2252, 2), (key2245, 2), (key2245, 2), (key2242, 2), (key2242, 2)]

def rawRow17668 : Integer.Sparse Key := [(key2060, 6), (key2030, -2), (key2060, -2), (key2068, -2), (key2149, 6), (key2030, -2), (key2149, -2), (key2165, -2), (key2149, -2), (key2242, -2), (key2245, -2), (key2060, -2), (key2242, -2), (key2252, -2), (key2060, 2), (key2068, 2), (key2149, 2), (key2165, 2), (key2245, 2), (key2252, 2)]

def rawRow17669 : Integer.Sparse Key := [(key2060, 6), (key2030, -2), (key2068, -2), (key2060, -2), (key2149, 6), (key2030, -2), (key2165, -2), (key2149, -2), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, -2), (key2252, -2), (key2242, -2), (key2068, 2), (key2060, 2), (key2165, 2), (key2149, 2), (key2252, 2), (key2245, 2)]

def rawRow17670 : Integer.Sparse Key := [(key2060, 6), (key2060, -2), (key2030, -2), (key2068, -2), (key2149, 6), (key2149, -2), (key2030, -2), (key2165, -2), (key2242, -2), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, -2), (key2252, -2), (key2149, 2), (key2245, 2), (key2060, 2), (key2252, 2), (key2068, 2), (key2165, 2)]

def rawRow17671 : Integer.Sparse Key := [(key2060, 6), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, 6), (key2149, -2), (key2165, -2), (key2030, -2), (key2242, -2), (key2245, -2), (key2149, -2), (key2242, -2), (key2252, -2), (key2060, -2), (key2245, 2), (key2149, 2), (key2252, 2), (key2060, 2), (key2165, 2), (key2068, 2)]

def rawRow17672 : Integer.Sparse Key := [(key2060, 6), (key2068, -2), (key2030, -2), (key2060, -2), (key2149, 6), (key2165, -2), (key2030, -2), (key2149, -2), (key2245, -2), (key2149, -2), (key2242, -2), (key2252, -2), (key2060, -2), (key2242, -2), (key2165, 2), (key2252, 2), (key2068, 2), (key2245, 2), (key2060, 2), (key2149, 2)]

def rawRow17673 : Integer.Sparse Key := [(key2060, 6), (key2068, -2), (key2060, -2), (key2030, -2), (key2149, 6), (key2165, -2), (key2149, -2), (key2030, -2), (key2245, -2), (key2242, -2), (key2149, -2), (key2252, -2), (key2242, -2), (key2060, -2), (key2252, 2), (key2165, 2), (key2245, 2), (key2068, 2), (key2149, 2), (key2060, 2)]

def rawRow17674 : Integer.Sparse Key := [(key2149, 6), (key2149, -2), (key2242, -2), (key2245, -2), (key2060, 6), (key2060, -2), (key2242, -2), (key2252, -2), (key2030, -2), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, -2), (key2165, -2), (key2060, 2), (key2068, 2), (key2149, 2), (key2165, 2), (key2245, 2), (key2252, 2)]

def rawRow17675 : Integer.Sparse Key := [(key2149, 6), (key2149, -2), (key2245, -2), (key2242, -2), (key2060, 6), (key2060, -2), (key2252, -2), (key2242, -2), (key2030, -2), (key2068, -2), (key2060, -2), (key2030, -2), (key2165, -2), (key2149, -2), (key2068, 2), (key2060, 2), (key2165, 2), (key2149, 2), (key2252, 2), (key2245, 2)]

def rawRow17676 : Integer.Sparse Key := [(key2149, 6), (key2242, -2), (key2149, -2), (key2245, -2), (key2060, 6), (key2242, -2), (key2060, -2), (key2252, -2), (key2060, -2), (key2030, -2), (key2068, -2), (key2149, -2), (key2030, -2), (key2165, -2), (key2149, 2), (key2245, 2), (key2060, 2), (key2252, 2), (key2068, 2), (key2165, 2)]

def rawRow17677 : Integer.Sparse Key := [(key2149, 6), (key2242, -2), (key2245, -2), (key2149, -2), (key2060, 6), (key2242, -2), (key2252, -2), (key2060, -2), (key2060, -2), (key2068, -2), (key2030, -2), (key2149, -2), (key2165, -2), (key2030, -2), (key2245, 2), (key2149, 2), (key2252, 2), (key2060, 2), (key2165, 2), (key2068, 2)]

def rawRow17678 : Integer.Sparse Key := [(key2149, 6), (key2245, -2), (key2149, -2), (key2242, -2), (key2060, 6), (key2252, -2), (key2060, -2), (key2242, -2), (key2068, -2), (key2030, -2), (key2060, -2), (key2165, -2), (key2030, -2), (key2149, -2), (key2165, 2), (key2252, 2), (key2068, 2), (key2245, 2), (key2060, 2), (key2149, 2)]

def rawRow17679 : Integer.Sparse Key := [(key2149, 6), (key2245, -2), (key2242, -2), (key2149, -2), (key2060, 6), (key2252, -2), (key2242, -2), (key2060, -2), (key2068, -2), (key2060, -2), (key2030, -2), (key2165, -2), (key2149, -2), (key2030, -2), (key2252, 2), (key2165, 2), (key2245, 2), (key2068, 2), (key2149, 2), (key2060, 2)]

def rawRow17680 : Integer.Sparse Key := [(key2242, 6), (key2149, -2), (key2149, -2), (key2245, -2), (key2242, 6), (key2060, -2), (key2060, -2), (key2252, -2), (key2149, -2), (key2149, -2), (key2245, -2), (key2060, -2), (key2060, -2), (key2252, -2), (key2030, 2), (key2068, 2), (key2030, 2), (key2165, 2), (key2068, 2), (key2165, 2)]

def rawRow17681 : Integer.Sparse Key := [(key2242, 6), (key2149, -2), (key2245, -2), (key2149, -2), (key2242, 6), (key2060, -2), (key2252, -2), (key2060, -2), (key2149, -2), (key2245, -2), (key2149, -2), (key2060, -2), (key2252, -2), (key2060, -2), (key2068, 2), (key2030, 2), (key2165, 2), (key2030, 2), (key2165, 2), (key2068, 2)]

def rawRow17682 : Integer.Sparse Key := [(key2242, 6), (key2245, -2), (key2149, -2), (key2149, -2), (key2242, 6), (key2252, -2), (key2060, -2), (key2060, -2), (key2245, -2), (key2149, -2), (key2149, -2), (key2252, -2), (key2060, -2), (key2060, -2), (key2165, 2), (key2165, 2), (key2068, 2), (key2068, 2), (key2030, 2), (key2030, 2)]

def rawRow17683 : Integer.Sparse Key := [(key704, -2), (key707, -2), (key707, -2), (key716, 6), (key704, -2), (key707, -2), (key707, -2), (key858, 2), (key861, 2), (key858, 2), (key884, 2), (key861, 2), (key884, 2), (key893, -2), (key893, -2), (key915, -2), (key716, 6), (key893, -2), (key893, -2), (key915, -2)]

def rawRow17684 : Integer.Sparse Key := [(key707, -2), (key704, -2), (key707, -2), (key716, 6), (key707, -2), (key704, -2), (key707, -2), (key861, 2), (key858, 2), (key884, 2), (key858, 2), (key884, 2), (key861, 2), (key893, -2), (key915, -2), (key893, -2), (key716, 6), (key893, -2), (key915, -2), (key893, -2)]

def rawRow17685 : Integer.Sparse Key := [(key707, -2), (key707, -2), (key704, -2), (key716, 6), (key707, -2), (key707, -2), (key704, -2), (key884, 2), (key884, 2), (key861, 2), (key861, 2), (key858, 2), (key858, 2), (key915, -2), (key893, -2), (key893, -2), (key716, 6), (key915, -2), (key893, -2), (key893, -2)]

def rawRow17686 : Integer.Sparse Key := [(key704, -2), (key707, -2), (key716, -2), (key707, 6), (key858, -2), (key861, -2), (key893, -2), (key704, 2), (key707, 2), (key858, 2), (key884, 2), (key893, 2), (key915, 2), (key707, -2), (key861, -2), (key884, -2), (key893, 6), (key716, -2), (key893, -2), (key915, -2)]

def rawRow17687 : Integer.Sparse Key := [(key707, -2), (key704, -2), (key716, -2), (key707, 6), (key861, -2), (key858, -2), (key893, -2), (key707, 2), (key704, 2), (key884, 2), (key858, 2), (key915, 2), (key893, 2), (key707, -2), (key884, -2), (key861, -2), (key893, 6), (key716, -2), (key915, -2), (key893, -2)]

def rawRow17688 : Integer.Sparse Key := [(key704, -2), (key716, -2), (key707, -2), (key707, 6), (key858, -2), (key893, -2), (key861, -2), (key858, 2), (key893, 2), (key704, 2), (key915, 2), (key707, 2), (key884, 2), (key861, -2), (key707, -2), (key884, -2), (key893, 6), (key893, -2), (key716, -2), (key915, -2)]

def rawRow17689 : Integer.Sparse Key := [(key716, -2), (key704, -2), (key707, -2), (key707, 6), (key893, -2), (key858, -2), (key861, -2), (key893, 2), (key858, 2), (key915, 2), (key704, 2), (key884, 2), (key707, 2), (key861, -2), (key884, -2), (key707, -2), (key893, 6), (key893, -2), (key915, -2), (key716, -2)]

def rawRow17690 : Integer.Sparse Key := [(key707, -2), (key716, -2), (key704, -2), (key707, 6), (key861, -2), (key893, -2), (key858, -2), (key884, 2), (key915, 2), (key707, 2), (key893, 2), (key704, 2), (key858, 2), (key884, -2), (key707, -2), (key861, -2), (key893, 6), (key915, -2), (key716, -2), (key893, -2)]

def rawRow17691 : Integer.Sparse Key := [(key716, -2), (key707, -2), (key704, -2), (key707, 6), (key893, -2), (key861, -2), (key858, -2), (key915, 2), (key884, 2), (key893, 2), (key707, 2), (key858, 2), (key704, 2), (key884, -2), (key861, -2), (key707, -2), (key893, 6), (key915, -2), (key893, -2), (key716, -2)]

def rawRow17692 : Integer.Sparse Key := [(key858, -2), (key861, -2), (key893, -2), (key893, 6), (key704, -2), (key707, -2), (key716, -2), (key704, 2), (key707, 2), (key858, 2), (key884, 2), (key893, 2), (key915, 2), (key716, -2), (key893, -2), (key915, -2), (key707, 6), (key707, -2), (key861, -2), (key884, -2)]

def rawRow17693 : Integer.Sparse Key := [(key861, -2), (key858, -2), (key893, -2), (key893, 6), (key707, -2), (key704, -2), (key716, -2), (key707, 2), (key704, 2), (key884, 2), (key858, 2), (key915, 2), (key893, 2), (key716, -2), (key915, -2), (key893, -2), (key707, 6), (key707, -2), (key884, -2), (key861, -2)]

def rawRow17694 : Integer.Sparse Key := [(key858, -2), (key893, -2), (key861, -2), (key893, 6), (key704, -2), (key716, -2), (key707, -2), (key858, 2), (key893, 2), (key704, 2), (key915, 2), (key707, 2), (key884, 2), (key893, -2), (key716, -2), (key915, -2), (key707, 6), (key861, -2), (key707, -2), (key884, -2)]

def rawRow17695 : Integer.Sparse Key := [(key893, -2), (key858, -2), (key861, -2), (key893, 6), (key716, -2), (key704, -2), (key707, -2), (key893, 2), (key858, 2), (key915, 2), (key704, 2), (key884, 2), (key707, 2), (key893, -2), (key915, -2), (key716, -2), (key707, 6), (key861, -2), (key884, -2), (key707, -2)]

def rawRow17696 : Integer.Sparse Key := [(key861, -2), (key893, -2), (key858, -2), (key893, 6), (key707, -2), (key716, -2), (key704, -2), (key884, 2), (key915, 2), (key707, 2), (key893, 2), (key704, 2), (key858, 2), (key915, -2), (key716, -2), (key893, -2), (key707, 6), (key884, -2), (key707, -2), (key861, -2)]

def rawRow17697 : Integer.Sparse Key := [(key893, -2), (key861, -2), (key858, -2), (key893, 6), (key716, -2), (key707, -2), (key704, -2), (key915, 2), (key884, 2), (key893, 2), (key707, 2), (key858, 2), (key704, 2), (key915, -2), (key893, -2), (key716, -2), (key707, 6), (key884, -2), (key861, -2), (key707, -2)]

def rawRow17698 : Integer.Sparse Key := [(key858, -2), (key893, -2), (key893, -2), (key861, 6), (key858, -2), (key893, -2), (key893, -2), (key704, 2), (key716, 2), (key704, 2), (key915, 2), (key716, 2), (key915, 2), (key707, -2), (key707, -2), (key884, -2), (key861, 6), (key707, -2), (key707, -2), (key884, -2)]

def rawRow17699 : Integer.Sparse Key := [(key893, -2), (key858, -2), (key893, -2), (key861, 6), (key893, -2), (key858, -2), (key893, -2), (key716, 2), (key704, 2), (key915, 2), (key704, 2), (key915, 2), (key716, 2), (key707, -2), (key884, -2), (key707, -2), (key861, 6), (key707, -2), (key884, -2), (key707, -2)]

def rawRow17700 : Integer.Sparse Key := [(key893, -2), (key893, -2), (key858, -2), (key861, 6), (key893, -2), (key893, -2), (key858, -2), (key915, 2), (key915, 2), (key716, 2), (key716, 2), (key704, 2), (key704, 2), (key884, -2), (key707, -2), (key707, -2), (key861, 6), (key884, -2), (key707, -2), (key707, -2)]

def rawRow17701 : Integer.Sparse Key := [(key862, 4), (key862, 4), (key887, 4), (key894, -2), (key896, -2), (key894, -2), (key917, -2), (key896, -2), (key917, -2), (key894, -2), (key896, -2), (key894, -2), (key917, -2), (key896, -2), (key917, -2), (key949, 4), (key949, 4), (key956, 4)]

def rawRow17702 : Integer.Sparse Key := [(key862, 4), (key887, 4), (key862, 4), (key896, -2), (key894, -2), (key917, -2), (key894, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key917, -2), (key894, -2), (key917, -2), (key896, -2), (key949, 4), (key956, 4), (key949, 4)]

def rawRow17703 : Integer.Sparse Key := [(key887, 4), (key862, 4), (key862, 4), (key917, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key894, -2), (key917, -2), (key917, -2), (key896, -2), (key896, -2), (key894, -2), (key894, -2), (key956, 4), (key949, 4), (key949, 4)]

def rawRow17704 : Integer.Sparse Key := [(key708, 4), (key894, 4), (key917, 4), (key708, -2), (key711, -2), (key862, -2), (key887, -2), (key896, -2), (key917, -2), (key717, -2), (key719, -2), (key894, -2), (key917, -2), (key949, -2), (key956, -2), (key719, 4), (key896, 4), (key917, 4)]

def rawRow17705 : Integer.Sparse Key := [(key708, 4), (key917, 4), (key894, 4), (key711, -2), (key708, -2), (key887, -2), (key862, -2), (key917, -2), (key896, -2), (key719, -2), (key717, -2), (key917, -2), (key894, -2), (key956, -2), (key949, -2), (key719, 4), (key917, 4), (key896, 4)]

def rawRow17706 : Integer.Sparse Key := [(key894, 4), (key708, 4), (key917, 4), (key862, -2), (key896, -2), (key708, -2), (key917, -2), (key711, -2), (key887, -2), (key894, -2), (key949, -2), (key717, -2), (key956, -2), (key719, -2), (key917, -2), (key896, 4), (key719, 4), (key917, 4)]

def rawRow17707 : Integer.Sparse Key := [(key894, 4), (key917, 4), (key708, 4), (key896, -2), (key862, -2), (key917, -2), (key708, -2), (key887, -2), (key711, -2), (key949, -2), (key894, -2), (key956, -2), (key717, -2), (key917, -2), (key719, -2), (key896, 4), (key917, 4), (key719, 4)]

def rawRow17708 : Integer.Sparse Key := [(key917, 4), (key708, 4), (key894, 4), (key887, -2), (key917, -2), (key711, -2), (key896, -2), (key708, -2), (key862, -2), (key917, -2), (key956, -2), (key719, -2), (key949, -2), (key717, -2), (key894, -2), (key917, 4), (key719, 4), (key896, 4)]

def rawRow17709 : Integer.Sparse Key := [(key917, 4), (key894, 4), (key708, 4), (key917, -2), (key887, -2), (key896, -2), (key711, -2), (key862, -2), (key708, -2), (key956, -2), (key917, -2), (key949, -2), (key719, -2), (key894, -2), (key717, -2), (key917, 4), (key896, 4), (key719, 4)]

def rawRow17710 : Integer.Sparse Key := [(key708, 4), (key894, 4), (key917, 4), (key717, -2), (key719, -2), (key894, -2), (key917, -2), (key949, -2), (key956, -2), (key708, -2), (key711, -2), (key862, -2), (key887, -2), (key896, -2), (key917, -2), (key719, 4), (key896, 4), (key917, 4)]

def rawRow17711 : Integer.Sparse Key := [(key708, 4), (key917, 4), (key894, 4), (key719, -2), (key717, -2), (key917, -2), (key894, -2), (key956, -2), (key949, -2), (key711, -2), (key708, -2), (key887, -2), (key862, -2), (key917, -2), (key896, -2), (key719, 4), (key917, 4), (key896, 4)]

def rawRow17712 : Integer.Sparse Key := [(key894, 4), (key708, 4), (key917, 4), (key894, -2), (key949, -2), (key717, -2), (key956, -2), (key719, -2), (key917, -2), (key862, -2), (key896, -2), (key708, -2), (key917, -2), (key711, -2), (key887, -2), (key896, 4), (key719, 4), (key917, 4)]

def rawRow17713 : Integer.Sparse Key := [(key894, 4), (key917, 4), (key708, 4), (key949, -2), (key894, -2), (key956, -2), (key717, -2), (key917, -2), (key719, -2), (key896, -2), (key862, -2), (key917, -2), (key708, -2), (key887, -2), (key711, -2), (key896, 4), (key917, 4), (key719, 4)]

def rawRow17714 : Integer.Sparse Key := [(key917, 4), (key708, 4), (key894, 4), (key917, -2), (key956, -2), (key719, -2), (key949, -2), (key717, -2), (key894, -2), (key887, -2), (key917, -2), (key711, -2), (key896, -2), (key708, -2), (key862, -2), (key917, 4), (key719, 4), (key896, 4)]

def rawRow17715 : Integer.Sparse Key := [(key917, 4), (key894, 4), (key708, 4), (key956, -2), (key917, -2), (key949, -2), (key719, -2), (key894, -2), (key717, -2), (key917, -2), (key887, -2), (key896, -2), (key711, -2), (key862, -2), (key708, -2), (key917, 4), (key896, 4), (key719, 4)]

def rawRow17716 : Integer.Sparse Key := [(key78, 4), (key717, 4), (key956, 4), (key708, -2), (key719, -2), (key708, -2), (key917, -2), (key719, -2), (key917, -2), (key708, -2), (key719, -2), (key708, -2), (key917, -2), (key719, -2), (key917, -2), (key711, 4), (key711, 4), (key887, 4)]

def rawRow17717 : Integer.Sparse Key := [(key78, 4), (key956, 4), (key717, 4), (key719, -2), (key708, -2), (key917, -2), (key708, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key917, -2), (key708, -2), (key917, -2), (key719, -2), (key711, 4), (key887, 4), (key711, 4)]

def rawRow17718 : Integer.Sparse Key := [(key191, 4), (key78, 4), (key717, 4), (key917, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key708, -2), (key917, -2), (key917, -2), (key719, -2), (key719, -2), (key708, -2), (key708, -2), (key887, 4), (key711, 4), (key711, 4)]

def rawRow17719 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2195, 2), (key2195, 2), (key2201, 2), (key2150, -1), (key2155, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2168, -1), (key2243, 2), (key2248, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2255, 2), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2311, -1), (key2195, 2), (key2195, 2), (key2201, 2), (key2304, -1), (key2306, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2311, -1)]

def rawRow17720 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2195, 2), (key2201, 2), (key2195, 2), (key2155, -1), (key2150, -1), (key2168, -1), (key2150, -1), (key2168, -1), (key2155, -1), (key2248, 2), (key2243, 2), (key2255, 2), (key2243, 2), (key2255, 2), (key2248, 2), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, -1), (key2306, -1), (key2195, 2), (key2201, 2), (key2195, 2), (key2306, -1), (key2304, -1), (key2311, -1), (key2304, -1), (key2311, -1), (key2306, -1)]

def rawRow17721 : Integer.Sparse Key := [(key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2201, 2), (key2195, 2), (key2195, 2), (key2168, -1), (key2168, -1), (key2155, -1), (key2155, -1), (key2150, -1), (key2150, -1), (key2255, 2), (key2255, 2), (key2248, 2), (key2248, 2), (key2243, 2), (key2243, 2), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, -1), (key2304, -1), (key2201, 2), (key2195, 2), (key2195, 2), (key2311, -1), (key2311, -1), (key2306, -1), (key2306, -1), (key2304, -1), (key2304, -1)]

def rawRow17722 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2036, 2), (key2155, 2), (key2168, 2), (key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, -1), (key2255, -1), (key2093, 2), (key2304, 2), (key2311, 2), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, -1), (key2311, -1)]

def rawRow17723 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2036, 2), (key2168, 2), (key2155, 2), (key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, -1), (key2248, -1), (key2093, 2), (key2311, 2), (key2304, 2), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, -1), (key2306, -1)]

def rawRow17724 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2155, 2), (key2036, 2), (key2168, 2), (key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, -1), (key2168, -1), (key2304, 2), (key2093, 2), (key2311, 2), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, -1), (key2201, -1)]

def rawRow17725 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2155, 2), (key2168, 2), (key2036, 2), (key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, -1), (key2071, -1), (key2304, 2), (key2311, 2), (key2093, 2), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, -1), (key2096, -1)]

def rawRow17726 : Integer.Sparse Key := [(key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2036, 2), (key2155, 2), (key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, -1), (key2155, -1), (key2311, 2), (key2093, 2), (key2304, 2), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, -1), (key2195, -1)]

def rawRow17727 : Integer.Sparse Key := [(key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2168, 2), (key2155, 2), (key2036, 2), (key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, -1), (key2066, -1), (key2311, 2), (key2304, 2), (key2093, 2), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, -1), (key2093, -1)]

def rawRow17728 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2243, -1), (key2255, -1), (key2304, -1), (key2311, -1), (key2093, 2), (key2304, 2), (key2311, 2), (key2031, -1), (key2036, -1), (key2150, -1), (key2168, -1), (key2195, -1), (key2201, -1), (key2061, 2), (key2071, 2), (key2150, 2), (key2168, 2), (key2306, 2), (key2311, 2), (key2093, -1), (key2096, -1), (key2195, -1), (key2201, -1), (key2306, -1), (key2311, -1), (key2036, 2), (key2155, 2), (key2168, 2), (key2066, -1), (key2071, -1), (key2155, -1), (key2168, -1), (key2248, -1), (key2255, -1)]

def rawRow17729 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2255, -1), (key2243, -1), (key2311, -1), (key2304, -1), (key2093, 2), (key2311, 2), (key2304, 2), (key2036, -1), (key2031, -1), (key2168, -1), (key2150, -1), (key2201, -1), (key2195, -1), (key2071, 2), (key2061, 2), (key2168, 2), (key2150, 2), (key2311, 2), (key2306, 2), (key2096, -1), (key2093, -1), (key2201, -1), (key2195, -1), (key2311, -1), (key2306, -1), (key2036, 2), (key2168, 2), (key2155, 2), (key2071, -1), (key2066, -1), (key2168, -1), (key2155, -1), (key2255, -1), (key2248, -1)]

def rawRow17730 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2061, -1), (key2311, -1), (key2066, -1), (key2255, -1), (key2304, 2), (key2093, 2), (key2311, 2), (key2150, -1), (key2195, -1), (key2031, -1), (key2201, -1), (key2036, -1), (key2168, -1), (key2150, 2), (key2306, 2), (key2061, 2), (key2311, 2), (key2071, 2), (key2168, 2), (key2195, -1), (key2306, -1), (key2093, -1), (key2311, -1), (key2096, -1), (key2201, -1), (key2155, 2), (key2036, 2), (key2168, 2), (key2155, -1), (key2248, -1), (key2066, -1), (key2255, -1), (key2071, -1), (key2168, -1)]

def rawRow17731 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2311, -1), (key2061, -1), (key2255, -1), (key2066, -1), (key2304, 2), (key2311, 2), (key2093, 2), (key2195, -1), (key2150, -1), (key2201, -1), (key2031, -1), (key2168, -1), (key2036, -1), (key2306, 2), (key2150, 2), (key2311, 2), (key2061, 2), (key2168, 2), (key2071, 2), (key2306, -1), (key2195, -1), (key2311, -1), (key2093, -1), (key2201, -1), (key2096, -1), (key2155, 2), (key2168, 2), (key2036, 2), (key2248, -1), (key2155, -1), (key2255, -1), (key2066, -1), (key2168, -1), (key2071, -1)]

def rawRow17732 : Integer.Sparse Key := [(key2255, -1), (key2311, -1), (key2066, -1), (key2304, -1), (key2061, -1), (key2243, -1), (key2311, 2), (key2093, 2), (key2304, 2), (key2168, -1), (key2201, -1), (key2036, -1), (key2195, -1), (key2031, -1), (key2150, -1), (key2168, 2), (key2311, 2), (key2071, 2), (key2306, 2), (key2061, 2), (key2150, 2), (key2201, -1), (key2311, -1), (key2096, -1), (key2306, -1), (key2093, -1), (key2195, -1), (key2168, 2), (key2036, 2), (key2155, 2), (key2168, -1), (key2255, -1), (key2071, -1), (key2248, -1), (key2066, -1), (key2155, -1)]

def rawRow17733 : Integer.Sparse Key := [(key2311, -1), (key2255, -1), (key2304, -1), (key2066, -1), (key2243, -1), (key2061, -1), (key2311, 2), (key2304, 2), (key2093, 2), (key2201, -1), (key2168, -1), (key2195, -1), (key2036, -1), (key2150, -1), (key2031, -1), (key2311, 2), (key2168, 2), (key2306, 2), (key2071, 2), (key2150, 2), (key2061, 2), (key2311, -1), (key2201, -1), (key2306, -1), (key2096, -1), (key2195, -1), (key2093, -1), (key2168, 2), (key2155, 2), (key2036, 2), (key2255, -1), (key2168, -1), (key2248, -1), (key2071, -1), (key2155, -1), (key2066, -1)]

def rawRow17734 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2066, 2), (key2066, 2), (key2255, 2), (key2061, -1), (key2093, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2311, -1), (key2031, 2), (key2096, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2201, 2), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2168, -1), (key2066, 2), (key2066, 2), (key2255, 2), (key2036, -1), (key2071, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2168, -1)]

def rawRow17735 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2066, 2), (key2255, 2), (key2066, 2), (key2093, -1), (key2061, -1), (key2311, -1), (key2061, -1), (key2311, -1), (key2093, -1), (key2096, 2), (key2031, 2), (key2201, 2), (key2031, 2), (key2201, 2), (key2096, 2), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, -1), (key2071, -1), (key2066, 2), (key2255, 2), (key2066, 2), (key2071, -1), (key2036, -1), (key2168, -1), (key2036, -1), (key2168, -1), (key2071, -1)]

def rawRow17736 : Integer.Sparse Key := [(key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2255, 2), (key2066, 2), (key2066, 2), (key2311, -1), (key2311, -1), (key2093, -1), (key2093, -1), (key2061, -1), (key2061, -1), (key2201, 2), (key2201, 2), (key2096, 2), (key2096, 2), (key2031, 2), (key2031, 2), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, -1), (key2036, -1), (key2255, 2), (key2066, 2), (key2066, 2), (key2168, -1), (key2168, -1), (key2071, -1), (key2071, -1), (key2036, -1), (key2036, -1)]

def rawRow17737 : Integer.Sparse Key := [(key2116, 4), (key2116, 4), (key2121, 4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2250, 12)]

def rawRow17738 : Integer.Sparse Key := [(key2116, 4), (key2121, 4), (key2116, 4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2250, 12)]

def rawRow17739 : Integer.Sparse Key := [(key2121, 4), (key2116, 4), (key2116, 4), (key2161, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2250, 12)]

def rawRow17740 : Integer.Sparse Key := [(key2116, 4), (key2158, 4), (key2161, 4), (key2116, -4), (key2121, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2250, -4), (key2161, 12)]

def rawRow17741 : Integer.Sparse Key := [(key2116, 4), (key2161, 4), (key2158, 4), (key2121, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2158, -4), (key2250, -4), (key2161, 12)]

def rawRow17742 : Integer.Sparse Key := [(key2158, 4), (key2116, 4), (key2161, 4), (key2116, -4), (key2161, -4), (key2121, -4), (key2158, -4), (key2250, -4), (key2161, -4), (key2161, 12)]

def rawRow17743 : Integer.Sparse Key := [(key2158, 4), (key2161, 4), (key2116, 4), (key2161, -4), (key2116, -4), (key2121, -4), (key2250, -4), (key2158, -4), (key2161, -4), (key2161, 12)]

def rawRow17744 : Integer.Sparse Key := [(key2161, 4), (key2116, 4), (key2158, 4), (key2121, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2250, -4), (key2158, -4), (key2161, 12)]

def rawRow17745 : Integer.Sparse Key := [(key2161, 4), (key2158, 4), (key2116, 4), (key2161, -4), (key2121, -4), (key2116, -4), (key2250, -4), (key2161, -4), (key2158, -4), (key2161, 12)]

def rawRow17746 : Integer.Sparse Key := [(key2116, 4), (key2158, 4), (key2161, 4), (key2158, -4), (key2161, -4), (key2250, -4), (key2116, -4), (key2121, -4), (key2161, -4), (key2161, 12)]

def rawRow17747 : Integer.Sparse Key := [(key2116, 4), (key2161, 4), (key2158, 4), (key2161, -4), (key2158, -4), (key2250, -4), (key2121, -4), (key2116, -4), (key2161, -4), (key2161, 12)]

def rawRow17748 : Integer.Sparse Key := [(key2158, 4), (key2116, 4), (key2161, 4), (key2158, -4), (key2250, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2121, -4), (key2161, 12)]

def rawRow17749 : Integer.Sparse Key := [(key2158, 4), (key2161, 4), (key2116, 4), (key2250, -4), (key2158, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2121, -4), (key2161, 12)]

def rawRow17750 : Integer.Sparse Key := [(key2161, 4), (key2116, 4), (key2158, 4), (key2161, -4), (key2250, -4), (key2158, -4), (key2121, -4), (key2161, -4), (key2116, -4), (key2161, 12)]

def rawRow17751 : Integer.Sparse Key := [(key2161, 4), (key2158, 4), (key2116, 4), (key2250, -4), (key2161, -4), (key2158, -4), (key2161, -4), (key2121, -4), (key2116, -4), (key2161, 12)]

def rawRow17752 : Integer.Sparse Key := [(key2158, 4), (key2158, 4), (key2250, 4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2121, 12)]

def rawRow17753 : Integer.Sparse Key := [(key2158, 4), (key2250, 4), (key2158, 4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2121, 12)]

def rawRow17754 : Integer.Sparse Key := [(key2250, 4), (key2158, 4), (key2158, 4), (key2161, -4), (key2161, -4), (key2116, -4), (key2161, -4), (key2161, -4), (key2116, -4), (key2121, 12)]

def rawRow17755 : Integer.Sparse Key := [(key1988, -2), (key1991, -2), (key1991, -2), (key2001, 6), (key1988, -2), (key1991, -2), (key1991, -2), (key2233, 2), (key2236, 2), (key2233, 2), (key2257, 2), (key2236, 2), (key2257, 2), (key2270, -2), (key2270, -2), (key2293, -2), (key2001, 6), (key2270, -2), (key2270, -2), (key2293, -2)]

def rawRow17756 : Integer.Sparse Key := [(key1991, -2), (key1988, -2), (key1991, -2), (key2001, 6), (key1991, -2), (key1988, -2), (key1991, -2), (key2236, 2), (key2233, 2), (key2257, 2), (key2233, 2), (key2257, 2), (key2236, 2), (key2270, -2), (key2293, -2), (key2270, -2), (key2001, 6), (key2270, -2), (key2293, -2), (key2270, -2)]

def rawRow17757 : Integer.Sparse Key := [(key1991, -2), (key1991, -2), (key1988, -2), (key2001, 6), (key1991, -2), (key1991, -2), (key1988, -2), (key2257, 2), (key2257, 2), (key2236, 2), (key2236, 2), (key2233, 2), (key2233, 2), (key2293, -2), (key2270, -2), (key2270, -2), (key2001, 6), (key2293, -2), (key2270, -2), (key2270, -2)]

def rawRow17758 : Integer.Sparse Key := [(key1988, -2), (key1991, -2), (key2001, -2), (key1991, 6), (key2233, -2), (key2236, -2), (key2270, -2), (key1988, 2), (key1991, 2), (key2233, 2), (key2257, 2), (key2270, 2), (key2293, 2), (key1991, -2), (key2236, -2), (key2257, -2), (key2270, 6), (key2001, -2), (key2270, -2), (key2293, -2)]

def rawRow17759 : Integer.Sparse Key := [(key1991, -2), (key1988, -2), (key2001, -2), (key1991, 6), (key2236, -2), (key2233, -2), (key2270, -2), (key1991, 2), (key1988, 2), (key2257, 2), (key2233, 2), (key2293, 2), (key2270, 2), (key1991, -2), (key2257, -2), (key2236, -2), (key2270, 6), (key2001, -2), (key2293, -2), (key2270, -2)]

def rawRow17760 : Integer.Sparse Key := [(key1988, -2), (key2001, -2), (key1991, -2), (key1991, 6), (key2233, -2), (key2270, -2), (key2236, -2), (key2233, 2), (key2270, 2), (key1988, 2), (key2293, 2), (key1991, 2), (key2257, 2), (key2236, -2), (key1991, -2), (key2257, -2), (key2270, 6), (key2270, -2), (key2001, -2), (key2293, -2)]

def rawRow17761 : Integer.Sparse Key := [(key2001, -2), (key1988, -2), (key1991, -2), (key1991, 6), (key2270, -2), (key2233, -2), (key2236, -2), (key2270, 2), (key2233, 2), (key2293, 2), (key1988, 2), (key2257, 2), (key1991, 2), (key2236, -2), (key2257, -2), (key1991, -2), (key2270, 6), (key2270, -2), (key2293, -2), (key2001, -2)]

def rawRow17762 : Integer.Sparse Key := [(key1991, -2), (key2001, -2), (key1988, -2), (key1991, 6), (key2236, -2), (key2270, -2), (key2233, -2), (key2257, 2), (key2293, 2), (key1991, 2), (key2270, 2), (key1988, 2), (key2233, 2), (key2257, -2), (key1991, -2), (key2236, -2), (key2270, 6), (key2293, -2), (key2001, -2), (key2270, -2)]

def rawRow17763 : Integer.Sparse Key := [(key2001, -2), (key1991, -2), (key1988, -2), (key1991, 6), (key2270, -2), (key2236, -2), (key2233, -2), (key2293, 2), (key2257, 2), (key2270, 2), (key1991, 2), (key2233, 2), (key1988, 2), (key2257, -2), (key2236, -2), (key1991, -2), (key2270, 6), (key2293, -2), (key2270, -2), (key2001, -2)]

def rawRow17764 : Integer.Sparse Key := [(key2233, -2), (key2236, -2), (key2270, -2), (key2270, 6), (key1988, -2), (key1991, -2), (key2001, -2), (key1988, 2), (key1991, 2), (key2233, 2), (key2257, 2), (key2270, 2), (key2293, 2), (key2001, -2), (key2270, -2), (key2293, -2), (key1991, 6), (key1991, -2), (key2236, -2), (key2257, -2)]

def rawRow17765 : Integer.Sparse Key := [(key2236, -2), (key2233, -2), (key2270, -2), (key2270, 6), (key1991, -2), (key1988, -2), (key2001, -2), (key1991, 2), (key1988, 2), (key2257, 2), (key2233, 2), (key2293, 2), (key2270, 2), (key2001, -2), (key2293, -2), (key2270, -2), (key1991, 6), (key1991, -2), (key2257, -2), (key2236, -2)]

def rawRow17766 : Integer.Sparse Key := [(key2233, -2), (key2270, -2), (key2236, -2), (key2270, 6), (key1988, -2), (key2001, -2), (key1991, -2), (key2233, 2), (key2270, 2), (key1988, 2), (key2293, 2), (key1991, 2), (key2257, 2), (key2270, -2), (key2001, -2), (key2293, -2), (key1991, 6), (key2236, -2), (key1991, -2), (key2257, -2)]

def rawRow17767 : Integer.Sparse Key := [(key2270, -2), (key2233, -2), (key2236, -2), (key2270, 6), (key2001, -2), (key1988, -2), (key1991, -2), (key2270, 2), (key2233, 2), (key2293, 2), (key1988, 2), (key2257, 2), (key1991, 2), (key2270, -2), (key2293, -2), (key2001, -2), (key1991, 6), (key2236, -2), (key2257, -2), (key1991, -2)]

def rawRow17768 : Integer.Sparse Key := [(key2236, -2), (key2270, -2), (key2233, -2), (key2270, 6), (key1991, -2), (key2001, -2), (key1988, -2), (key2257, 2), (key2293, 2), (key1991, 2), (key2270, 2), (key1988, 2), (key2233, 2), (key2293, -2), (key2001, -2), (key2270, -2), (key1991, 6), (key2257, -2), (key1991, -2), (key2236, -2)]

def rawRow17769 : Integer.Sparse Key := [(key2270, -2), (key2236, -2), (key2233, -2), (key2270, 6), (key2001, -2), (key1991, -2), (key1988, -2), (key2293, 2), (key2257, 2), (key2270, 2), (key1991, 2), (key2233, 2), (key1988, 2), (key2293, -2), (key2270, -2), (key2001, -2), (key1991, 6), (key2257, -2), (key2236, -2), (key1991, -2)]

def rawRow17770 : Integer.Sparse Key := [(key2233, -2), (key2270, -2), (key2270, -2), (key2236, 6), (key2233, -2), (key2270, -2), (key2270, -2), (key1988, 2), (key2001, 2), (key1988, 2), (key2293, 2), (key2001, 2), (key2293, 2), (key1991, -2), (key1991, -2), (key2257, -2), (key2236, 6), (key1991, -2), (key1991, -2), (key2257, -2)]

def rawRow17771 : Integer.Sparse Key := [(key2270, -2), (key2233, -2), (key2270, -2), (key2236, 6), (key2270, -2), (key2233, -2), (key2270, -2), (key2001, 2), (key1988, 2), (key2293, 2), (key1988, 2), (key2293, 2), (key2001, 2), (key1991, -2), (key2257, -2), (key1991, -2), (key2236, 6), (key1991, -2), (key2257, -2), (key1991, -2)]

def rawRow17772 : Integer.Sparse Key := [(key2270, -2), (key2270, -2), (key2233, -2), (key2236, 6), (key2270, -2), (key2270, -2), (key2233, -2), (key2293, 2), (key2293, 2), (key2001, 2), (key2001, 2), (key1988, 2), (key1988, 2), (key2257, -2), (key1991, -2), (key1991, -2), (key2236, 6), (key2257, -2), (key1991, -2), (key1991, -2)]

def rawRow17773 : Integer.Sparse Key := [(key772, 4), (key772, 4), (key780, 4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key874, 12)]

def rawRow17774 : Integer.Sparse Key := [(key772, 4), (key780, 4), (key772, 4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key874, 12)]

def rawRow17775 : Integer.Sparse Key := [(key780, 4), (key772, 4), (key772, 4), (key805, -4), (key805, -4), (key799, -4), (key805, -4), (key805, -4), (key799, -4), (key874, 12)]

def rawRow17776 : Integer.Sparse Key := [(key772, 4), (key799, 4), (key805, 4), (key772, -4), (key780, -4), (key805, -4), (key799, -4), (key805, -4), (key874, -4), (key805, 12)]

def rawRow17777 : Integer.Sparse Key := [(key772, 4), (key805, 4), (key799, 4), (key780, -4), (key772, -4), (key805, -4), (key805, -4), (key799, -4), (key874, -4), (key805, 12)]

def rawRow17778 : Integer.Sparse Key := [(key799, 4), (key772, 4), (key805, 4), (key772, -4), (key805, -4), (key780, -4), (key799, -4), (key874, -4), (key805, -4), (key805, 12)]

def rawRow17779 : Integer.Sparse Key := [(key799, 4), (key805, 4), (key772, 4), (key805, -4), (key772, -4), (key780, -4), (key874, -4), (key799, -4), (key805, -4), (key805, 12)]

def rawRow17780 : Integer.Sparse Key := [(key805, 4), (key772, 4), (key799, 4), (key780, -4), (key805, -4), (key772, -4), (key805, -4), (key874, -4), (key799, -4), (key805, 12)]

def rawRow17781 : Integer.Sparse Key := [(key805, 4), (key799, 4), (key772, 4), (key805, -4), (key780, -4), (key772, -4), (key874, -4), (key805, -4), (key799, -4), (key805, 12)]

def rawRow17782 : Integer.Sparse Key := [(key772, 4), (key799, 4), (key805, 4), (key799, -4), (key805, -4), (key874, -4), (key772, -4), (key780, -4), (key805, -4), (key805, 12)]

def rawRow17783 : Integer.Sparse Key := [(key772, 4), (key805, 4), (key799, 4), (key805, -4), (key799, -4), (key874, -4), (key780, -4), (key772, -4), (key805, -4), (key805, 12)]

def rawRow17784 : Integer.Sparse Key := [(key799, 4), (key772, 4), (key805, 4), (key799, -4), (key874, -4), (key805, -4), (key772, -4), (key805, -4), (key780, -4), (key805, 12)]

def rawRow17785 : Integer.Sparse Key := [(key799, 4), (key805, 4), (key772, 4), (key874, -4), (key799, -4), (key805, -4), (key805, -4), (key772, -4), (key780, -4), (key805, 12)]

def rawRow17786 : Integer.Sparse Key := [(key805, 4), (key772, 4), (key799, 4), (key805, -4), (key874, -4), (key799, -4), (key780, -4), (key805, -4), (key772, -4), (key805, 12)]

def rawRow17787 : Integer.Sparse Key := [(key805, 4), (key799, 4), (key772, 4), (key874, -4), (key805, -4), (key799, -4), (key805, -4), (key780, -4), (key772, -4), (key805, 12)]

def rawRow17788 : Integer.Sparse Key := [(key799, 4), (key799, 4), (key874, 4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key780, 12)]

def rawRow17789 : Integer.Sparse Key := [(key799, 4), (key874, 4), (key799, 4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key780, 12)]

def rawRow17790 : Integer.Sparse Key := [(key874, 4), (key799, 4), (key799, 4), (key805, -4), (key805, -4), (key772, -4), (key805, -4), (key805, -4), (key772, -4), (key780, 12)]

def rawRow17791 : Integer.Sparse Key := [(key2150, -1), (key2153, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2167, -1), (key2177, 2), (key2177, 2), (key2188, 2), (key2150, -1), (key2153, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2167, -1), (key2243, 2), (key2247, 2), (key2243, 2), (key2254, 2), (key2247, 2), (key2254, 2), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2288, -1), (key2177, 2), (key2177, 2), (key2188, 2), (key2277, -1), (key2280, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2288, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17792 : Integer.Sparse Key := [(key2153, -1), (key2150, -1), (key2167, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2177, 2), (key2188, 2), (key2177, 2), (key2153, -1), (key2150, -1), (key2167, -1), (key2150, -1), (key2167, -1), (key2153, -1), (key2247, 2), (key2243, 2), (key2254, 2), (key2243, 2), (key2254, 2), (key2247, 2), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, -1), (key2280, -1), (key2177, 2), (key2188, 2), (key2177, 2), (key2280, -1), (key2277, -1), (key2288, -1), (key2277, -1), (key2288, -1), (key2280, -1)]

def rawRow17793 : Integer.Sparse Key := [(key2167, -1), (key2167, -1), (key2153, -1), (key2153, -1), (key2150, -1), (key2150, -1), (key2188, 2), (key2177, 2), (key2177, 2), (key2167, -1), (key2167, -1), (key2153, -1), (key2153, -1), (key2150, -1), (key2150, -1), (key2254, 2), (key2254, 2), (key2247, 2), (key2247, 2), (key2243, 2), (key2243, 2), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, -1), (key2277, -1), (key2188, 2), (key2177, 2), (key2177, 2), (key2288, -1), (key2288, -1), (key2280, -1), (key2280, -1), (key2277, -1), (key2277, -1)]

def rawRow17794 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2150, -1), (key2167, -1), (key2177, -1), (key2188, -1), (key2034, 2), (key2153, 2), (key2167, 2), (key2061, -1), (key2064, -1), (key2243, -1), (key2254, -1), (key2277, -1), (key2288, -1), (key2061, 2), (key2070, 2), (key2150, 2), (key2167, 2), (key2280, 2), (key2288, 2), (key2064, -1), (key2070, -1), (key2153, -1), (key2167, -1), (key2247, -1), (key2254, -1), (key2080, 2), (key2277, 2), (key2288, 2), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, -1), (key2288, -1)]

def rawRow17795 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2167, -1), (key2150, -1), (key2188, -1), (key2177, -1), (key2034, 2), (key2167, 2), (key2153, 2), (key2064, -1), (key2061, -1), (key2254, -1), (key2243, -1), (key2288, -1), (key2277, -1), (key2070, 2), (key2061, 2), (key2167, 2), (key2150, 2), (key2288, 2), (key2280, 2), (key2070, -1), (key2064, -1), (key2167, -1), (key2153, -1), (key2254, -1), (key2247, -1), (key2080, 2), (key2288, 2), (key2277, 2), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, -1), (key2280, -1)]

def rawRow17796 : Integer.Sparse Key := [(key2150, -1), (key2177, -1), (key2031, -1), (key2188, -1), (key2034, -1), (key2167, -1), (key2153, 2), (key2034, 2), (key2167, 2), (key2243, -1), (key2277, -1), (key2061, -1), (key2288, -1), (key2064, -1), (key2254, -1), (key2150, 2), (key2280, 2), (key2061, 2), (key2288, 2), (key2070, 2), (key2167, 2), (key2153, -1), (key2247, -1), (key2064, -1), (key2254, -1), (key2070, -1), (key2167, -1), (key2277, 2), (key2080, 2), (key2288, 2), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, -1), (key2188, -1)]

def rawRow17797 : Integer.Sparse Key := [(key2177, -1), (key2150, -1), (key2188, -1), (key2031, -1), (key2167, -1), (key2034, -1), (key2153, 2), (key2167, 2), (key2034, 2), (key2277, -1), (key2243, -1), (key2288, -1), (key2061, -1), (key2254, -1), (key2064, -1), (key2280, 2), (key2150, 2), (key2288, 2), (key2061, 2), (key2167, 2), (key2070, 2), (key2247, -1), (key2153, -1), (key2254, -1), (key2064, -1), (key2167, -1), (key2070, -1), (key2277, 2), (key2288, 2), (key2080, 2), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, -1), (key2086, -1)]

def rawRow17798 : Integer.Sparse Key := [(key2167, -1), (key2188, -1), (key2034, -1), (key2177, -1), (key2031, -1), (key2150, -1), (key2167, 2), (key2034, 2), (key2153, 2), (key2254, -1), (key2288, -1), (key2064, -1), (key2277, -1), (key2061, -1), (key2243, -1), (key2167, 2), (key2288, 2), (key2070, 2), (key2280, 2), (key2061, 2), (key2150, 2), (key2167, -1), (key2254, -1), (key2070, -1), (key2247, -1), (key2064, -1), (key2153, -1), (key2288, 2), (key2080, 2), (key2277, 2), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, -1), (key2177, -1)]

def rawRow17799 : Integer.Sparse Key := [(key2188, -1), (key2167, -1), (key2177, -1), (key2034, -1), (key2150, -1), (key2031, -1), (key2167, 2), (key2153, 2), (key2034, 2), (key2288, -1), (key2254, -1), (key2277, -1), (key2064, -1), (key2243, -1), (key2061, -1), (key2288, 2), (key2167, 2), (key2280, 2), (key2070, 2), (key2150, 2), (key2061, 2), (key2254, -1), (key2167, -1), (key2247, -1), (key2070, -1), (key2153, -1), (key2064, -1), (key2288, 2), (key2277, 2), (key2080, 2), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, -1), (key2080, -1)]

def rawRow17800 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2243, -1), (key2254, -1), (key2277, -1), (key2288, -1), (key2080, 2), (key2277, 2), (key2288, 2), (key2031, -1), (key2034, -1), (key2150, -1), (key2167, -1), (key2177, -1), (key2188, -1), (key2061, 2), (key2070, 2), (key2150, 2), (key2167, 2), (key2280, 2), (key2288, 2), (key2080, -1), (key2086, -1), (key2177, -1), (key2188, -1), (key2280, -1), (key2288, -1), (key2034, 2), (key2153, 2), (key2167, 2), (key2064, -1), (key2070, -1), (key2153, -1), (key2167, -1), (key2247, -1), (key2254, -1)]

def rawRow17801 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2254, -1), (key2243, -1), (key2288, -1), (key2277, -1), (key2080, 2), (key2288, 2), (key2277, 2), (key2034, -1), (key2031, -1), (key2167, -1), (key2150, -1), (key2188, -1), (key2177, -1), (key2070, 2), (key2061, 2), (key2167, 2), (key2150, 2), (key2288, 2), (key2280, 2), (key2086, -1), (key2080, -1), (key2188, -1), (key2177, -1), (key2288, -1), (key2280, -1), (key2034, 2), (key2167, 2), (key2153, 2), (key2070, -1), (key2064, -1), (key2167, -1), (key2153, -1), (key2254, -1), (key2247, -1)]

def rawRow17802 : Integer.Sparse Key := [(key2243, -1), (key2277, -1), (key2061, -1), (key2288, -1), (key2064, -1), (key2254, -1), (key2277, 2), (key2080, 2), (key2288, 2), (key2150, -1), (key2177, -1), (key2031, -1), (key2188, -1), (key2034, -1), (key2167, -1), (key2150, 2), (key2280, 2), (key2061, 2), (key2288, 2), (key2070, 2), (key2167, 2), (key2177, -1), (key2280, -1), (key2080, -1), (key2288, -1), (key2086, -1), (key2188, -1), (key2153, 2), (key2034, 2), (key2167, 2), (key2153, -1), (key2247, -1), (key2064, -1), (key2254, -1), (key2070, -1), (key2167, -1)]

def rawRow17803 : Integer.Sparse Key := [(key2277, -1), (key2243, -1), (key2288, -1), (key2061, -1), (key2254, -1), (key2064, -1), (key2277, 2), (key2288, 2), (key2080, 2), (key2177, -1), (key2150, -1), (key2188, -1), (key2031, -1), (key2167, -1), (key2034, -1), (key2280, 2), (key2150, 2), (key2288, 2), (key2061, 2), (key2167, 2), (key2070, 2), (key2280, -1), (key2177, -1), (key2288, -1), (key2080, -1), (key2188, -1), (key2086, -1), (key2153, 2), (key2167, 2), (key2034, 2), (key2247, -1), (key2153, -1), (key2254, -1), (key2064, -1), (key2167, -1), (key2070, -1)]

def rawRow17804 : Integer.Sparse Key := [(key2254, -1), (key2288, -1), (key2064, -1), (key2277, -1), (key2061, -1), (key2243, -1), (key2288, 2), (key2080, 2), (key2277, 2), (key2167, -1), (key2188, -1), (key2034, -1), (key2177, -1), (key2031, -1), (key2150, -1), (key2167, 2), (key2288, 2), (key2070, 2), (key2280, 2), (key2061, 2), (key2150, 2), (key2188, -1), (key2288, -1), (key2086, -1), (key2280, -1), (key2080, -1), (key2177, -1), (key2167, 2), (key2034, 2), (key2153, 2), (key2167, -1), (key2254, -1), (key2070, -1), (key2247, -1), (key2064, -1), (key2153, -1)]

def rawRow17805 : Integer.Sparse Key := [(key2288, -1), (key2254, -1), (key2277, -1), (key2064, -1), (key2243, -1), (key2061, -1), (key2288, 2), (key2277, 2), (key2080, 2), (key2188, -1), (key2167, -1), (key2177, -1), (key2034, -1), (key2150, -1), (key2031, -1), (key2288, 2), (key2167, 2), (key2280, 2), (key2070, 2), (key2150, 2), (key2061, 2), (key2288, -1), (key2188, -1), (key2280, -1), (key2086, -1), (key2177, -1), (key2080, -1), (key2167, 2), (key2153, 2), (key2034, 2), (key2254, -1), (key2167, -1), (key2247, -1), (key2070, -1), (key2153, -1), (key2064, -1)]

def rawRow17806 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2288, -1), (key2064, 2), (key2064, 2), (key2254, 2), (key2061, -1), (key2080, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2288, -1), (key2031, 2), (key2086, 2), (key2031, 2), (key2188, 2), (key2086, 2), (key2188, 2), (key2034, -1), (key2070, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2167, -1), (key2064, 2), (key2064, 2), (key2254, 2), (key2034, -1), (key2070, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2167, -1)]

def rawRow17807 : Integer.Sparse Key := [(key2080, -1), (key2061, -1), (key2288, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2064, 2), (key2254, 2), (key2064, 2), (key2080, -1), (key2061, -1), (key2288, -1), (key2061, -1), (key2288, -1), (key2080, -1), (key2086, 2), (key2031, 2), (key2188, 2), (key2031, 2), (key2188, 2), (key2086, 2), (key2070, -1), (key2034, -1), (key2167, -1), (key2034, -1), (key2167, -1), (key2070, -1), (key2064, 2), (key2254, 2), (key2064, 2), (key2070, -1), (key2034, -1), (key2167, -1), (key2034, -1), (key2167, -1), (key2070, -1)]

def rawRow17808 : Integer.Sparse Key := [(key2288, -1), (key2288, -1), (key2080, -1), (key2080, -1), (key2061, -1), (key2061, -1), (key2254, 2), (key2064, 2), (key2064, 2), (key2288, -1), (key2288, -1), (key2080, -1), (key2080, -1), (key2061, -1), (key2061, -1), (key2188, 2), (key2188, 2), (key2086, 2), (key2086, 2), (key2031, 2), (key2031, 2), (key2167, -1), (key2167, -1), (key2070, -1), (key2070, -1), (key2034, -1), (key2034, -1), (key2254, 2), (key2064, 2), (key2064, 2), (key2167, -1), (key2167, -1), (key2070, -1), (key2070, -1), (key2034, -1), (key2034, -1)]

def rawRow17809 : Integer.Sparse Key := [(key361, -2), (key364, -2), (key364, -2), (key368, 6), (key361, -2), (key364, -2), (key364, -2), (key530, 2), (key534, 2), (key530, 2), (key634, 2), (key534, 2), (key634, 2), (key540, -2), (key540, -2), (key639, -2), (key368, 6), (key540, -2), (key540, -2), (key639, -2)]

def rawRow17810 : Integer.Sparse Key := [(key364, -2), (key361, -2), (key364, -2), (key368, 6), (key364, -2), (key361, -2), (key364, -2), (key534, 2), (key530, 2), (key634, 2), (key530, 2), (key634, 2), (key534, 2), (key540, -2), (key639, -2), (key540, -2), (key368, 6), (key540, -2), (key639, -2), (key540, -2)]

def rawRow17811 : Integer.Sparse Key := [(key364, -2), (key364, -2), (key361, -2), (key368, 6), (key364, -2), (key364, -2), (key361, -2), (key634, 2), (key634, 2), (key534, 2), (key534, 2), (key530, 2), (key530, 2), (key639, -2), (key540, -2), (key540, -2), (key368, 6), (key639, -2), (key540, -2), (key540, -2)]

def rawRow17812 : Integer.Sparse Key := [(key361, -2), (key364, -2), (key368, -2), (key364, 6), (key530, -2), (key534, -2), (key540, -2), (key361, 2), (key364, 2), (key530, 2), (key634, 2), (key540, 2), (key639, 2), (key364, -2), (key534, -2), (key634, -2), (key540, 6), (key368, -2), (key540, -2), (key639, -2)]

def rawRow17813 : Integer.Sparse Key := [(key364, -2), (key361, -2), (key368, -2), (key364, 6), (key534, -2), (key530, -2), (key540, -2), (key364, 2), (key361, 2), (key634, 2), (key530, 2), (key639, 2), (key540, 2), (key364, -2), (key634, -2), (key534, -2), (key540, 6), (key368, -2), (key639, -2), (key540, -2)]

def rawRow17814 : Integer.Sparse Key := [(key361, -2), (key368, -2), (key364, -2), (key364, 6), (key530, -2), (key540, -2), (key534, -2), (key530, 2), (key540, 2), (key361, 2), (key639, 2), (key364, 2), (key634, 2), (key534, -2), (key364, -2), (key634, -2), (key540, 6), (key540, -2), (key368, -2), (key639, -2)]

def rawRow17815 : Integer.Sparse Key := [(key368, -2), (key361, -2), (key364, -2), (key364, 6), (key540, -2), (key530, -2), (key534, -2), (key540, 2), (key530, 2), (key639, 2), (key361, 2), (key634, 2), (key364, 2), (key534, -2), (key634, -2), (key364, -2), (key540, 6), (key540, -2), (key639, -2), (key368, -2)]

def rawRow17816 : Integer.Sparse Key := [(key364, -2), (key368, -2), (key361, -2), (key364, 6), (key534, -2), (key540, -2), (key530, -2), (key634, 2), (key639, 2), (key364, 2), (key540, 2), (key361, 2), (key530, 2), (key634, -2), (key364, -2), (key534, -2), (key540, 6), (key639, -2), (key368, -2), (key540, -2)]

def rawRow17817 : Integer.Sparse Key := [(key368, -2), (key364, -2), (key361, -2), (key364, 6), (key540, -2), (key534, -2), (key530, -2), (key639, 2), (key634, 2), (key540, 2), (key364, 2), (key530, 2), (key361, 2), (key634, -2), (key534, -2), (key364, -2), (key540, 6), (key639, -2), (key540, -2), (key368, -2)]

def rawRow17818 : Integer.Sparse Key := [(key530, -2), (key534, -2), (key540, -2), (key540, 6), (key361, -2), (key364, -2), (key368, -2), (key361, 2), (key364, 2), (key530, 2), (key634, 2), (key540, 2), (key639, 2), (key368, -2), (key540, -2), (key639, -2), (key364, 6), (key364, -2), (key534, -2), (key634, -2)]

def rawRow17819 : Integer.Sparse Key := [(key534, -2), (key530, -2), (key540, -2), (key540, 6), (key364, -2), (key361, -2), (key368, -2), (key364, 2), (key361, 2), (key634, 2), (key530, 2), (key639, 2), (key540, 2), (key368, -2), (key639, -2), (key540, -2), (key364, 6), (key364, -2), (key634, -2), (key534, -2)]

def rawRow17820 : Integer.Sparse Key := [(key530, -2), (key540, -2), (key534, -2), (key540, 6), (key361, -2), (key368, -2), (key364, -2), (key530, 2), (key540, 2), (key361, 2), (key639, 2), (key364, 2), (key634, 2), (key540, -2), (key368, -2), (key639, -2), (key364, 6), (key534, -2), (key364, -2), (key634, -2)]

def rawRow17821 : Integer.Sparse Key := [(key540, -2), (key530, -2), (key534, -2), (key540, 6), (key368, -2), (key361, -2), (key364, -2), (key540, 2), (key530, 2), (key639, 2), (key361, 2), (key634, 2), (key364, 2), (key540, -2), (key639, -2), (key368, -2), (key364, 6), (key534, -2), (key634, -2), (key364, -2)]

def rawRow17822 : Integer.Sparse Key := [(key534, -2), (key540, -2), (key530, -2), (key540, 6), (key364, -2), (key368, -2), (key361, -2), (key634, 2), (key639, 2), (key364, 2), (key540, 2), (key361, 2), (key530, 2), (key639, -2), (key368, -2), (key540, -2), (key364, 6), (key634, -2), (key364, -2), (key534, -2)]

def rawRow17823 : Integer.Sparse Key := [(key540, -2), (key534, -2), (key530, -2), (key540, 6), (key368, -2), (key364, -2), (key361, -2), (key639, 2), (key634, 2), (key540, 2), (key364, 2), (key530, 2), (key361, 2), (key639, -2), (key540, -2), (key368, -2), (key364, 6), (key634, -2), (key534, -2), (key364, -2)]

def rawRow17824 : Integer.Sparse Key := [(key530, -2), (key540, -2), (key540, -2), (key534, 6), (key530, -2), (key540, -2), (key540, -2), (key361, 2), (key368, 2), (key361, 2), (key639, 2), (key368, 2), (key639, 2), (key364, -2), (key364, -2), (key634, -2), (key534, 6), (key364, -2), (key364, -2), (key634, -2)]

def rawRow17825 : Integer.Sparse Key := [(key540, -2), (key530, -2), (key540, -2), (key534, 6), (key540, -2), (key530, -2), (key540, -2), (key368, 2), (key361, 2), (key639, 2), (key361, 2), (key639, 2), (key368, 2), (key364, -2), (key634, -2), (key364, -2), (key534, 6), (key364, -2), (key634, -2), (key364, -2)]

def rawRow17826 : Integer.Sparse Key := [(key540, -2), (key540, -2), (key530, -2), (key534, 6), (key540, -2), (key540, -2), (key530, -2), (key639, 2), (key639, 2), (key368, 2), (key368, 2), (key361, 2), (key361, 2), (key634, -2), (key364, -2), (key364, -2), (key534, 6), (key634, -2), (key364, -2), (key364, -2)]

def rawRow17827 : Integer.Sparse Key := [(key1992, 2), (key1992, 2), (key1995, 2), (key2002, -2), (key2004, -2), (key2004, -2), (key1992, 2), (key1992, 2), (key1995, 2), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2295, -1), (key2002, -2), (key2004, -2), (key2004, -2), (key2271, -1), (key2273, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2295, -1), (key2325, 4), (key2325, 4), (key2337, 4)]

def rawRow17828 : Integer.Sparse Key := [(key1992, 2), (key1995, 2), (key1992, 2), (key2004, -2), (key2002, -2), (key2004, -2), (key1992, 2), (key1995, 2), (key1992, 2), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2004, -2), (key2002, -2), (key2004, -2), (key2273, -1), (key2271, -1), (key2295, -1), (key2271, -1), (key2295, -1), (key2273, -1), (key2325, 4), (key2337, 4), (key2325, 4)]

def rawRow17829 : Integer.Sparse Key := [(key1995, 2), (key1992, 2), (key1992, 2), (key2004, -2), (key2004, -2), (key2002, -2), (key1995, 2), (key1992, 2), (key1992, 2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2271, -1), (key2004, -2), (key2004, -2), (key2002, -2), (key2295, -1), (key2295, -1), (key2273, -1), (key2273, -1), (key2271, -1), (key2271, -1), (key2337, 4), (key2325, 4), (key2325, 4)]

def rawRow17830 : Integer.Sparse Key := [(key1992, 2), (key2002, 2), (key2004, 2), (key1992, -2), (key1995, -2), (key2004, -2), (key2237, 2), (key2271, 2), (key2273, 2), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, -1), (key2295, -1), (key2271, -2), (key2273, -2), (key2325, -2), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, -1), (key2337, -1), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17831 : Integer.Sparse Key := [(key1992, 2), (key2004, 2), (key2002, 2), (key1995, -2), (key1992, -2), (key2004, -2), (key2237, 2), (key2273, 2), (key2271, 2), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, -1), (key2273, -1), (key2273, -2), (key2271, -2), (key2325, -2), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, -1), (key2325, -1), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17832 : Integer.Sparse Key := [(key2002, 2), (key1992, 2), (key2004, 2), (key1992, -2), (key2004, -2), (key1995, -2), (key2271, 2), (key2237, 2), (key2273, 2), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, -1), (key2260, -1), (key2271, -2), (key2325, -2), (key2273, -2), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, -1), (key2295, -1), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17833 : Integer.Sparse Key := [(key2002, 2), (key2004, 2), (key1992, 2), (key2004, -2), (key1992, -2), (key1995, -2), (key2271, 2), (key2273, 2), (key2237, 2), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, -1), (key1995, -1), (key2325, -2), (key2271, -2), (key2273, -2), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, -1), (key2004, -1), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17834 : Integer.Sparse Key := [(key2004, 2), (key1992, 2), (key2002, 2), (key1995, -2), (key2004, -2), (key1992, -2), (key2273, 2), (key2237, 2), (key2271, 2), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, -1), (key2237, -1), (key2273, -2), (key2325, -2), (key2271, -2), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, -1), (key2271, -1), (key2295, 4), (key2004, 4), (key2273, 4)]

def rawRow17835 : Integer.Sparse Key := [(key2004, 2), (key2002, 2), (key1992, 2), (key2004, -2), (key1995, -2), (key1992, -2), (key2273, 2), (key2271, 2), (key2237, 2), (key2295, -1), (key2260, -1), (key2273, -1), (key1995, -1), (key2237, -1), (key1992, -1), (key2325, -2), (key2273, -2), (key2271, -2), (key2337, -1), (key2295, -1), (key2325, -1), (key2004, -1), (key2271, -1), (key2002, -1), (key2295, 4), (key2273, 4), (key2004, 4)]

def rawRow17836 : Integer.Sparse Key := [(key2237, 2), (key2271, 2), (key2273, 2), (key2271, -2), (key2273, -2), (key2325, -2), (key1992, 2), (key2002, 2), (key2004, 2), (key2002, -1), (key2004, -1), (key2271, -1), (key2295, -1), (key2325, -1), (key2337, -1), (key1992, -2), (key1995, -2), (key2004, -2), (key1992, -1), (key1995, -1), (key2237, -1), (key2260, -1), (key2273, -1), (key2295, -1), (key2004, 4), (key2273, 4), (key2295, 4)]

def rawRow17837 : Integer.Sparse Key := [(key2237, 2), (key2273, 2), (key2271, 2), (key2273, -2), (key2271, -2), (key2325, -2), (key1992, 2), (key2004, 2), (key2002, 2), (key2004, -1), (key2002, -1), (key2295, -1), (key2271, -1), (key2337, -1), (key2325, -1), (key1995, -2), (key1992, -2), (key2004, -2), (key1995, -1), (key1992, -1), (key2260, -1), (key2237, -1), (key2295, -1), (key2273, -1), (key2004, 4), (key2295, 4), (key2273, 4)]

def rawRow17838 : Integer.Sparse Key := [(key2271, 2), (key2237, 2), (key2273, 2), (key2271, -2), (key2325, -2), (key2273, -2), (key2002, 2), (key1992, 2), (key2004, 2), (key2271, -1), (key2325, -1), (key2002, -1), (key2337, -1), (key2004, -1), (key2295, -1), (key1992, -2), (key2004, -2), (key1995, -2), (key2237, -1), (key2273, -1), (key1992, -1), (key2295, -1), (key1995, -1), (key2260, -1), (key2273, 4), (key2004, 4), (key2295, 4)]

def rawRow17839 : Integer.Sparse Key := [(key2271, 2), (key2273, 2), (key2237, 2), (key2325, -2), (key2271, -2), (key2273, -2), (key2002, 2), (key2004, 2), (key1992, 2), (key2325, -1), (key2271, -1), (key2337, -1), (key2002, -1), (key2295, -1), (key2004, -1), (key2004, -2), (key1992, -2), (key1995, -2), (key2273, -1), (key2237, -1), (key2295, -1), (key1992, -1), (key2260, -1), (key1995, -1), (key2273, 4), (key2295, 4), (key2004, 4)]

def rawRow17840 : Integer.Sparse Key := [(key2273, 2), (key2237, 2), (key2271, 2), (key2273, -2), (key2325, -2), (key2271, -2), (key2004, 2), (key1992, 2), (key2002, 2), (key2295, -1), (key2337, -1), (key2004, -1), (key2325, -1), (key2002, -1), (key2271, -1), (key1995, -2), (key2004, -2), (key1992, -2), (key2260, -1), (key2295, -1), (key1995, -1), (key2273, -1), (key1992, -1), (key2237, -1), (key2295, 4), (key2004, 4), (key2273, 4)]

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

def rawRow17953 : Integer.Sparse Key := [(key636, 4), (key636, 4), (key637, 4), (key642, -4), (key643, -4), (key643, -4), (key642, -4), (key643, -4), (key643, -4), (key651, 12)]

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

def rawRow1734 : Integer.Sparse Key := [(key2617, -2), (key2655, -2), (key2655, -2), (key2620, 1), (key2620, 1), (key2643, 1), (key2643, 1), (key2656, 1), (key2656, 1), (key2810, 2), (key2899, 2), (key2899, 2), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, -1), (key2915, -1), (key2952, -1), (key2952, -1), (key2978, -1), (key2978, -1), (key2999, -1), (key2999, -1), (key2945, 1), (key2945, 1), (key2962, 1), (key2962, 1), (key3004, 1), (key3004, 1)]

def rawRow1735 : Integer.Sparse Key := [(key2655, -2), (key2617, -2), (key2655, -2), (key2643, 1), (key2656, 1), (key2620, 1), (key2656, 1), (key2620, 1), (key2643, 1), (key2899, 2), (key2810, 2), (key2899, 2), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2978, -1), (key2999, -1), (key2952, -1), (key2999, -1), (key2952, -1), (key2978, -1), (key2962, 1), (key3004, 1), (key2945, 1), (key3004, 1), (key2945, 1), (key2962, 1)]

def rawRow1736 : Integer.Sparse Key := [(key2655, -2), (key2655, -2), (key2617, -2), (key2656, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2643, 1), (key2620, 1), (key2899, 2), (key2899, 2), (key2810, 2), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, -1), (key2797, -1), (key2999, -1), (key2978, -1), (key2999, -1), (key2952, -1), (key2978, -1), (key2952, -1), (key3004, 1), (key2962, 1), (key3004, 1), (key2945, 1), (key2962, 1), (key2945, 1)]

def rawRow1737 : Integer.Sparse Key := [(key2620, -2), (key2643, -2), (key2656, -2), (key2617, 1), (key2620, 1), (key2633, 1), (key2643, 1), (key2650, 1), (key2655, 1), (key2833, 2), (key2906, 2), (key2915, 2), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, -1), (key2906, -1), (key2962, -1), (key2964, -1), (key2985, -1), (key2994, -1), (key3001, -1), (key3004, -1), (key2940, 1), (key2946, 1), (key2952, 1), (key2964, 1), (key2999, 1), (key3001, 1)]

def rawRow1738 : Integer.Sparse Key := [(key2620, -2), (key2656, -2), (key2643, -2), (key2620, 1), (key2617, 1), (key2643, 1), (key2633, 1), (key2655, 1), (key2650, 1), (key2833, 2), (key2915, 2), (key2906, 2), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2899, -1), (key2964, -1), (key2962, -1), (key2994, -1), (key2985, -1), (key3004, -1), (key3001, -1), (key2946, 1), (key2940, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2999, 1)]

def rawRow1739 : Integer.Sparse Key := [(key2643, -2), (key2620, -2), (key2656, -2), (key2633, 1), (key2643, 1), (key2617, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2906, 2), (key2833, 2), (key2915, 2), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2985, -1), (key3001, -1), (key2962, -1), (key3004, -1), (key2964, -1), (key2994, -1), (key2952, 1), (key2999, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2964, 1)]

def rawRow1740 : Integer.Sparse Key := [(key2643, -2), (key2656, -2), (key2620, -2), (key2643, 1), (key2633, 1), (key2655, 1), (key2617, 1), (key2643, 1), (key2620, 1), (key2906, 2), (key2915, 2), (key2833, 2), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, -1), (key2797, -1), (key3001, -1), (key2985, -1), (key3004, -1), (key2962, -1), (key2994, -1), (key2964, -1), (key2999, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2964, 1), (key2946, 1)]

def rawRow1741 : Integer.Sparse Key := [(key2656, -2), (key2620, -2), (key2643, -2), (key2650, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2617, 1), (key2633, 1), (key2915, 2), (key2833, 2), (key2906, 2), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, -1), (key2810, -1), (key2994, -1), (key3004, -1), (key2964, -1), (key3001, -1), (key2962, -1), (key2985, -1), (key2964, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2940, 1), (key2952, 1)]

def rawRow1742 : Integer.Sparse Key := [(key2656, -2), (key2643, -2), (key2620, -2), (key2655, 1), (key2650, 1), (key2643, 1), (key2620, 1), (key2633, 1), (key2617, 1), (key2915, 2), (key2906, 2), (key2833, 2), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key3004, -1), (key2994, -1), (key3001, -1), (key2964, -1), (key2985, -1), (key2962, -1), (key3001, 1), (key2964, 1), (key2999, 1), (key2946, 1), (key2952, 1), (key2940, 1)]

def rawRow1743 : Integer.Sparse Key := [(key2810, -2), (key2899, -2), (key2899, -2), (key2833, 1), (key2833, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1), (key2617, 2), (key2655, 2), (key2655, 2), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, -1), (key3004, -1), (key2620, -1), (key2620, -1), (key2643, -1), (key2643, -1), (key2656, -1), (key2656, -1), (key2797, 1), (key2797, 1), (key2833, 1), (key2833, 1), (key2915, 1), (key2915, 1)]

def rawRow1744 : Integer.Sparse Key := [(key2899, -2), (key2810, -2), (key2899, -2), (key2906, 1), (key2915, 1), (key2833, 1), (key2915, 1), (key2833, 1), (key2906, 1), (key2655, 2), (key2617, 2), (key2655, 2), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2620, -1), (key2656, -1), (key2620, -1), (key2643, -1), (key2833, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, 1), (key2833, 1)]

def rawRow1745 : Integer.Sparse Key := [(key2899, -2), (key2899, -2), (key2810, -2), (key2915, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2906, 1), (key2833, 1), (key2655, 2), (key2655, 2), (key2617, 2), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2656, -1), (key2620, -1), (key2643, -1), (key2620, -1), (key2915, 1), (key2833, 1), (key2915, 1), (key2797, 1), (key2833, 1), (key2797, 1)]

def rawRow1746 : Integer.Sparse Key := [(key2797, -2), (key2833, -2), (key2915, -2), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2833, 1), (key2906, 1), (key2945, 2), (key2962, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2730, -1), (key2751, -1), (key2833, -1), (key2915, -1), (key2964, -1), (key2994, -1), (key2620, 1), (key2656, 1), (key2675, 1), (key2751, 1), (key2946, 1), (key2964, 1)]

def rawRow1747 : Integer.Sparse Key := [(key2797, -2), (key2915, -2), (key2833, -2), (key2797, 1), (key2787, 1), (key2899, 1), (key2810, 1), (key2906, 1), (key2833, 1), (key2945, 2), (key3004, 2), (key2962, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2751, -1), (key2730, -1), (key2915, -1), (key2833, -1), (key2994, -1), (key2964, -1), (key2656, 1), (key2620, 1), (key2751, 1), (key2675, 1), (key2964, 1), (key2946, 1)]

def rawRow1748 : Integer.Sparse Key := [(key2833, -2), (key2797, -2), (key2915, -2), (key2810, 1), (key2833, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2962, 2), (key2945, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2833, -1), (key2964, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2675, 1), (key2946, 1), (key2620, 1), (key2964, 1), (key2656, 1), (key2751, 1)]

def rawRow1749 : Integer.Sparse Key := [(key2833, -2), (key2915, -2), (key2797, -2), (key2833, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2899, 1), (key2797, 1), (key2962, 2), (key3004, 2), (key2945, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2915, -1), (key2751, -1), (key2946, 1), (key2675, 1), (key2964, 1), (key2620, 1), (key2751, 1), (key2656, 1)]

def rawRow1750 : Integer.Sparse Key := [(key2915, -2), (key2797, -2), (key2833, -2), (key2899, 1), (key2906, 1), (key2797, 1), (key2833, 1), (key2787, 1), (key2810, 1), (key3004, 2), (key2945, 2), (key2962, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2730, -1), (key2833, -1), (key2751, 1), (key2964, 1), (key2656, 1), (key2946, 1), (key2620, 1), (key2675, 1)]

def rawRow1751 : Integer.Sparse Key := [(key2915, -2), (key2833, -2), (key2797, -2), (key2906, 1), (key2899, 1), (key2833, 1), (key2797, 1), (key2810, 1), (key2787, 1), (key3004, 2), (key2962, 2), (key2945, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2964, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2964, 1), (key2751, 1), (key2946, 1), (key2656, 1), (key2675, 1), (key2620, 1)]

def rawRow1752 : Integer.Sparse Key := [(key2952, -2), (key2978, -2), (key2999, -2), (key2962, 1), (key2964, 1), (key2985, 1), (key3001, 1), (key2994, 1), (key3004, 1), (key2620, 2), (key2643, 2), (key2656, 2), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2633, -1), (key2643, -1), (key2650, -1), (key2655, -1), (key2787, 1), (key2797, 1), (key2810, 1), (key2833, 1), (key2899, 1), (key2906, 1)]

def rawRow1753 : Integer.Sparse Key := [(key2952, -2), (key2999, -2), (key2978, -2), (key2964, 1), (key2962, 1), (key3001, 1), (key2985, 1), (key3004, 1), (key2994, 1), (key2620, 2), (key2656, 2), (key2643, 2), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2643, -1), (key2633, -1), (key2655, -1), (key2650, -1), (key2797, 1), (key2787, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2899, 1)]

def rawRow1754 : Integer.Sparse Key := [(key2978, -2), (key2952, -2), (key2999, -2), (key2985, 1), (key2994, 1), (key2962, 1), (key3004, 1), (key2964, 1), (key3001, 1), (key2643, 2), (key2620, 2), (key2656, 2), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2617, -1), (key2655, -1), (key2620, -1), (key2643, -1), (key2810, 1), (key2899, 1), (key2787, 1), (key2906, 1), (key2797, 1), (key2833, 1)]

def rawRow1755 : Integer.Sparse Key := [(key2978, -2), (key2999, -2), (key2952, -2), (key2994, 1), (key2985, 1), (key3004, 1), (key2962, 1), (key3001, 1), (key2964, 1), (key2643, 2), (key2656, 2), (key2620, 2), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2655, -1), (key2617, -1), (key2643, -1), (key2620, -1), (key2899, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2833, 1), (key2797, 1)]

def rawRow1756 : Integer.Sparse Key := [(key2999, -2), (key2952, -2), (key2978, -2), (key3001, 1), (key3004, 1), (key2964, 1), (key2994, 1), (key2962, 1), (key2985, 1), (key2656, 2), (key2620, 2), (key2643, 2), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, -1), (key2833, -1), (key2650, -1), (key2655, -1), (key2620, -1), (key2643, -1), (key2617, -1), (key2633, -1), (key2833, 1), (key2906, 1), (key2797, 1), (key2899, 1), (key2787, 1), (key2810, 1)]

def rawRow1757 : Integer.Sparse Key := [(key2999, -2), (key2978, -2), (key2952, -2), (key3004, 1), (key3001, 1), (key2994, 1), (key2964, 1), (key2985, 1), (key2962, 1), (key2656, 2), (key2643, 2), (key2620, 2), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, -1), (key2730, -1), (key2655, -1), (key2650, -1), (key2643, -1), (key2620, -1), (key2633, -1), (key2617, -1), (key2906, 1), (key2833, 1), (key2899, 1), (key2797, 1), (key2810, 1), (key2787, 1)]

def rawRow1758 : Integer.Sparse Key := [(key2945, -2), (key2962, -2), (key3004, -2), (key2940, 1), (key2946, 1), (key2952, 1), (key2999, 1), (key2964, 1), (key3001, 1), (key2797, 2), (key2833, 2), (key2915, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2617, 1), (key2655, 1), (key2672, 1), (key2749, 1), (key2945, 1), (key2962, 1)]

def rawRow1759 : Integer.Sparse Key := [(key2945, -2), (key3004, -2), (key2962, -2), (key2946, 1), (key2940, 1), (key2999, 1), (key2952, 1), (key3001, 1), (key2964, 1), (key2797, 2), (key2915, 2), (key2833, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2797, -1), (key2787, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2833, -1), (key2655, 1), (key2617, 1), (key2749, 1), (key2672, 1), (key2962, 1), (key2945, 1)]

def rawRow1760 : Integer.Sparse Key := [(key2962, -2), (key2945, -2), (key3004, -2), (key2952, 1), (key2964, 1), (key2940, 1), (key3001, 1), (key2946, 1), (key2999, 1), (key2833, 2), (key2797, 2), (key2915, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2787, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2672, 1), (key2749, 1), (key2617, 1), (key2962, 1), (key2655, 1), (key2749, 1)]

def rawRow1761 : Integer.Sparse Key := [(key2962, -2), (key3004, -2), (key2945, -2), (key2964, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2999, 1), (key2946, 1), (key2833, 2), (key2915, 2), (key2797, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2899, -1), (key2797, -1), (key2749, 1), (key2672, 1), (key2962, 1), (key2617, 1), (key2749, 1), (key2655, 1)]

def rawRow1762 : Integer.Sparse Key := [(key3004, -2), (key2945, -2), (key2962, -2), (key2999, 1), (key3001, 1), (key2946, 1), (key2964, 1), (key2940, 1), (key2952, 1), (key2915, 2), (key2797, 2), (key2833, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2899, -1), (key2906, -1), (key2797, -1), (key2833, -1), (key2787, -1), (key2810, -1), (key2945, 1), (key2962, 1), (key2655, 1), (key2749, 1), (key2617, 1), (key2672, 1)]

def rawRow1763 : Integer.Sparse Key := [(key3004, -2), (key2962, -2), (key2945, -2), (key3001, 1), (key2999, 1), (key2964, 1), (key2946, 1), (key2952, 1), (key2940, 1), (key2915, 2), (key2833, 2), (key2797, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2906, -1), (key2899, -1), (key2833, -1), (key2797, -1), (key2810, -1), (key2787, -1), (key2962, 1), (key2945, 1), (key2749, 1), (key2655, 1), (key2672, 1), (key2617, 1)]

def rawRow1778 : Integer.Sparse Key := [(key1250, -6), (key1250, 2), (key1250, 2), (key1269, 2), (key1525, 6), (key1525, -2), (key1525, -2), (key1892, -2), (key1603, -2), (key1603, -2), (key1677, -2), (key1603, 2), (key1603, 2), (key1914, 2)]

def rawRow1779 : Integer.Sparse Key := [(key1250, -6), (key1250, 2), (key1269, 2), (key1250, 2), (key1525, 6), (key1525, -2), (key1892, -2), (key1525, -2), (key1603, -2), (key1677, -2), (key1603, -2), (key1603, 2), (key1914, 2), (key1603, 2)]

def rawRow1780 : Integer.Sparse Key := [(key1250, -6), (key1269, 2), (key1250, 2), (key1250, 2), (key1525, 6), (key1892, -2), (key1525, -2), (key1525, -2), (key1677, -2), (key1603, -2), (key1603, -2), (key1914, 2), (key1603, 2), (key1603, 2)]

def rawRow1782 : Integer.Sparse Key := [(key1525, -6), (key1603, 2), (key1603, 2), (key1677, 2), (key1250, 6), (key1603, -2), (key1603, -2), (key1914, -2), (key1250, -2), (key1250, -2), (key1269, -2), (key1525, 2), (key1525, 2), (key1892, 2)]

def rawRow1783 : Integer.Sparse Key := [(key1525, -6), (key1603, 2), (key1677, 2), (key1603, 2), (key1250, 6), (key1603, -2), (key1914, -2), (key1603, -2), (key1250, -2), (key1269, -2), (key1250, -2), (key1525, 2), (key1892, 2), (key1525, 2)]

def rawRow1784 : Integer.Sparse Key := [(key1525, -6), (key1677, 2), (key1603, 2), (key1603, 2), (key1250, 6), (key1914, -2), (key1603, -2), (key1603, -2), (key1269, -2), (key1250, -2), (key1250, -2), (key1892, 2), (key1525, 2), (key1525, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined16 : Sparse := combined16_part0 ++ combined16_part1

end MUB6.TaoCertificate

end OAI
end


