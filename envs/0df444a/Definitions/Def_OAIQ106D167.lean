-- Prove2me | Definitions.Def_OAIQ106D167
-- name    : OAIQ106D167
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:31:43.283142+00:00
-- url     : https://prove2.me/theorems/fc856246-23c7-4d1d-90f1-c274975bfca4
-- title:
--   Definitions bundle OAIQ106D167 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 769 declarations of OpenAI's Lean: 769 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow19002`, `OAI.MUB6.Certificate.GramRows.rawRow19003`, `OAI.MUB6.Certificate.GramRows.rawRow19004`, `OAI.MUB6.Certificate.GramRows.rawRow19005`, `OAI.MUB6.Certificate.GramRows.rawRow19006`, `OAI.MUB6.Certificate.GramRows.rawRow19007`, `OAI.MUB6.Certificate.GramRows.rawRow19008`, `OAI.MUB6.Certificate.GramRows.rawRow19009`, `OAI.MUB6.Certificate.GramRows.rawRow19010`, `OAI.MUB6.Certificate.GramRows.rawRow19011`, `OAI.MUB6.Certificate.GramRows.rawRow19012`, `OAI.MUB6.Certificate.GramRows.rawRow19013`, `OAI.MUB6.Certificate.GramRows.rawRow19014`, `OAI.MUB6.Certificate.GramRows.rawRow19015`, `OAI.MUB6.Certificate.GramRows.rawRow19016`, `OAI.MUB6.Certificate.GramRows.rawRow19017`, `OAI.MUB6.Certificate.GramRows.rawRow19018`, `OAI.MUB6.Certificate.GramRows.rawRow19019`, `OAI.MUB6.Certificate.GramRows.rawRow19020`, `OAI.MUB6.Certificate.GramRows.rawRow19021`, `OAI.MUB6.Certificate.GramRows.rawRow19022`, `OAI.MUB6.Certificate.GramRows.rawRow19023`, `OAI.MUB6.Certificate.GramRows.rawRow19024`, `OAI.MUB6.Certificate.GramRows.rawRow19025`, `OAI.MUB6.Certificate.GramRows.rawRow19026`, `OAI.MUB6.Certificate.GramRows.rawRow19027`, `OAI.MUB6.Certificate.GramRows.rawRow19028`, `OAI.MUB6.Certificate.GramRows.rawRow19029`, `OAI.MUB6.Certificate.GramRows.rawRow19030`, `OAI.MUB6.Certificate.GramRows.rawRow19031`, `OAI.MUB6.Certificate.GramRows.rawRow19032`, `OAI.MUB6.Certificate.GramRows.rawRow19033`, `OAI.MUB6.Certificate.GramRows.rawRow19034`, `OAI.MUB6.Certificate.GramRows.rawRow19035`, `OAI.MUB6.Certificate.GramRows.rawRow19036`, `OAI.MUB6.Certificate.GramRows.rawRow19037`, `OAI.MUB6.Certificate.GramRows.rawRow19038`, `OAI.MUB6.Certificate.GramRows.rawRow19039`, `OAI.MUB6.Certificate.GramRows.rawRow1904`, `OAI.MUB6.Certificate.GramRows.rawRow19040` and 729 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block172`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block172.lean), [`MutuallyUnbiased_GramRows_Block173`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block173.lean), [`MutuallyUnbiased_GramRows_Block174`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block174.lean), [`MutuallyUnbiased_GramRows_Block175`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block175.lean), [`MutuallyUnbiased_GramRows_Block176`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block176.lean), [`MutuallyUnbiased_GramRows_Block177`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block177.lean), [`MutuallyUnbiased_GramRows_Block178`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block178.lean), [`MutuallyUnbiased_GramRows_Block38`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block38.lean), [`MutuallyUnbiased_GramRows_Block39`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block39.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D085`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow7` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19002 : Integer.Sparse Key := [(key2352, 24), (key2511, 24), (key2447, 24), (key2447, 24), (key2447, 24)]

def rawRow19003 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2447, 24), (key2447, 24), (key2511, 24)]

def rawRow19004 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2447, 24), (key2511, 24), (key2447, 24)]

def rawRow19005 : Integer.Sparse Key := [(key2447, 24), (key2352, 24), (key2511, 24), (key2447, 24), (key2447, 24)]

def rawRow19006 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2352, 24), (key2447, 24), (key2511, 24)]

def rawRow19007 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2352, 24), (key2511, 24), (key2447, 24)]

def rawRow19008 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2447, 24), (key2352, 24), (key2511, 24)]

def rawRow19009 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2447, 24), (key2511, 24), (key2352, 24)]

def rawRow19010 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2511, 24), (key2352, 24), (key2447, 24)]

def rawRow19011 : Integer.Sparse Key := [(key2447, 24), (key2447, 24), (key2511, 24), (key2447, 24), (key2352, 24)]

def rawRow19012 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2352, 24), (key2447, 24), (key2447, 24)]

def rawRow19013 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2447, 24), (key2352, 24), (key2447, 24)]

def rawRow19014 : Integer.Sparse Key := [(key2447, 24), (key2511, 24), (key2447, 24), (key2447, 24), (key2352, 24)]

def rawRow19015 : Integer.Sparse Key := [(key2511, 24), (key2352, 24), (key2447, 24), (key2447, 24), (key2447, 24)]

def rawRow19016 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2352, 24), (key2447, 24), (key2447, 24)]

def rawRow19017 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2447, 24), (key2352, 24), (key2447, 24)]

def rawRow19018 : Integer.Sparse Key := [(key2511, 24), (key2447, 24), (key2447, 24), (key2447, 24), (key2352, 24)]

def rawRow19019 : Integer.Sparse Key := [(key972, 6), (key977, 6), (key977, 6), (key977, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key1218, 6)]

def rawRow19020 : Integer.Sparse Key := [(key977, 6), (key972, 6), (key977, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key1162, 6)]

def rawRow19021 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key972, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key1162, 6)]

def rawRow19022 : Integer.Sparse Key := [(key977, 6), (key977, 6), (key977, 6), (key972, 6), (key1181, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key1162, 6)]

def rawRow19023 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key972, 6), (key977, 6), (key977, 6), (key1086, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1181, 6), (key1162, 6), (key1162, 6), (key1218, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6)]

def rawRow19024 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key977, 6), (key972, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1218, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6)]

def rawRow19025 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, 6), (key977, 6), (key972, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key1162, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6)]

def rawRow19026 : Integer.Sparse Key := [(key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key972, 6), (key977, 6), (key1086, 6), (key1181, 6), (key1162, 6), (key1218, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1181, 6)]

def rawRow19027 : Integer.Sparse Key := [(key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key977, 6), (key972, 6), (key1181, 6), (key1086, 6), (key1218, 6), (key1162, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1181, 6), (key1091, 6)]

def rawRow19028 : Integer.Sparse Key := [(key1086, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1162, 6), (key972, 6), (key1218, 6), (key977, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1181, 6)]

def rawRow19029 : Integer.Sparse Key := [(key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1218, 6), (key972, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key977, 6)]

def rawRow19030 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1086, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, 6), (key1218, 6), (key977, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1181, 6), (key977, 6), (key1091, 6)]

def rawRow19031 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1086, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1218, 6), (key1181, 6), (key1162, 6), (key977, 6), (key1086, 6), (key972, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1181, 6), (key1091, 6), (key977, 6)]

def rawRow19032 : Integer.Sparse Key := [(key1091, 6), (key1091, 6), (key1162, 6), (key1086, 6), (key1181, 6), (key1181, 6), (key1218, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1086, 6), (key1181, 6), (key977, 6), (key1091, 6), (key1091, 6)]

def rawRow19033 : Integer.Sparse Key := [(key1091, 6), (key1162, 6), (key1091, 6), (key1086, 6), (key1181, 6), (key1218, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1086, 6), (key972, 6), (key1086, 6), (key1181, 6), (key1091, 6), (key977, 6), (key1091, 6)]

def rawRow19034 : Integer.Sparse Key := [(key1162, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key1218, 6), (key1181, 6), (key1181, 6), (key1162, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1091, 6), (key977, 6), (key1086, 6), (key1086, 6), (key972, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key977, 6)]

def rawRow19035 : Integer.Sparse Key := [(key1181, 6), (key1181, 6), (key1181, 6), (key1218, 6), (key977, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key1162, 6), (key972, 6), (key1086, 6), (key1086, 6), (key1086, 6)]

def rawRow19036 : Integer.Sparse Key := [(key1181, 6), (key1181, 6), (key1218, 6), (key1181, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1091, 6), (key1086, 6), (key972, 6), (key1086, 6), (key1086, 6)]

def rawRow19037 : Integer.Sparse Key := [(key1181, 6), (key1218, 6), (key1181, 6), (key1181, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1162, 6), (key977, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1086, 6), (key1086, 6), (key972, 6), (key1086, 6)]

def rawRow19038 : Integer.Sparse Key := [(key1218, 6), (key1181, 6), (key1181, 6), (key1181, 6), (key1162, 6), (key1091, 6), (key1091, 6), (key1162, 6), (key1091, 6), (key1162, 6), (key977, 6), (key1091, 6), (key977, 6), (key1091, 6), (key1091, 6), (key977, 6), (key1086, 6), (key1086, 6), (key1086, 6), (key972, 6)]

def rawRow19039 : Integer.Sparse Key := [(key2361, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2531, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2561, 4)]

def rawRow19040 : Integer.Sparse Key := [(key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2561, 4), (key2520, 4)]

def rawRow19041 : Integer.Sparse Key := [(key2364, 4), (key2361, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2520, 4)]

def rawRow19042 : Integer.Sparse Key := [(key2364, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2361, 4), (key2361, 4), (key2531, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow19043 : Integer.Sparse Key := [(key2456, 4), (key2456, 4), (key2459, 4), (key2517, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2531, 4), (key2517, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2561, 4), (key2361, 4), (key2364, 4), (key2364, 4), (key2456, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2561, 4)]

def rawRow19044 : Integer.Sparse Key := [(key2456, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2520, 4), (key2361, 4), (key2364, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2561, 4), (key2517, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2361, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2531, 4), (key2456, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2561, 4), (key2520, 4)]

def rawRow19045 : Integer.Sparse Key := [(key2459, 4), (key2456, 4), (key2456, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2364, 4), (key2361, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2520, 4), (key2520, 4), (key2517, 4), (key2517, 4), (key2364, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2531, 4), (key2459, 4), (key2459, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2520, 4)]

def rawRow19046 : Integer.Sparse Key := [(key2456, 4), (key2517, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2520, 4), (key2361, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2531, 4), (key2520, 4), (key2561, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2361, 4), (key2364, 4), (key2456, 4), (key2531, 4), (key2520, 4), (key2561, 4), (key2364, 4), (key2459, 4), (key2531, 4)]

def rawRow19047 : Integer.Sparse Key := [(key2456, 4), (key2520, 4), (key2517, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2517, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2364, 4), (key2361, 4), (key2531, 4), (key2456, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2531, 4), (key2459, 4)]

def rawRow19048 : Integer.Sparse Key := [(key2517, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2517, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2456, 4), (key2520, 4), (key2361, 4), (key2561, 4), (key2364, 4), (key2531, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2361, 4), (key2561, 4), (key2364, 4), (key2531, 4), (key2459, 4), (key2364, 4), (key2531, 4)]

def rawRow19049 : Integer.Sparse Key := [(key2517, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2517, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2520, 4), (key2456, 4), (key2561, 4), (key2361, 4), (key2531, 4), (key2364, 4), (key2520, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2561, 4), (key2361, 4), (key2531, 4), (key2364, 4), (key2459, 4), (key2531, 4), (key2364, 4)]

def rawRow19050 : Integer.Sparse Key := [(key2520, 4), (key2456, 4), (key2517, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2561, 4), (key2361, 4), (key2517, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2364, 4), (key2459, 4)]

def rawRow19051 : Integer.Sparse Key := [(key2520, 4), (key2517, 4), (key2456, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2520, 4), (key2517, 4), (key2456, 4), (key2561, 4), (key2517, 4), (key2361, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2364, 4), (key2456, 4), (key2361, 4), (key2520, 4), (key2459, 4), (key2456, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2364, 4), (key2456, 4), (key2361, 4), (key2531, 4), (key2459, 4), (key2364, 4)]

def rawRow19052 : Integer.Sparse Key := [(key2459, 4), (key2520, 4), (key2520, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2531, 4), (key2561, 4), (key2561, 4), (key2364, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow19053 : Integer.Sparse Key := [(key2520, 4), (key2459, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow19054 : Integer.Sparse Key := [(key2520, 4), (key2520, 4), (key2459, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2561, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2517, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2361, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2364, 4), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow19055 : Integer.Sparse Key := [(key2531, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2561, 4), (key2561, 4), (key2364, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2520, 4), (key2361, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2517, 4)]

def rawRow19056 : Integer.Sparse Key := [(key2531, 4), (key2561, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2561, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2364, 4), (key2459, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2456, 4)]

def rawRow19057 : Integer.Sparse Key := [(key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2361, 4), (key2456, 4)]

def rawRow19058 : Integer.Sparse Key := [(key2561, 4), (key2561, 4), (key2531, 4), (key2561, 4), (key2531, 4), (key2531, 4), (key2520, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2520, 4), (key2364, 4), (key2520, 4), (key2459, 4), (key2520, 4), (key2364, 4), (key2459, 4), (key2364, 4), (key2517, 4), (key2456, 4), (key2456, 4), (key2517, 4), (key2456, 4), (key2517, 4), (key2361, 4), (key2456, 4), (key2361, 4), (key2456, 4), (key2456, 4), (key2361, 4)]

def rawRow19059 : Integer.Sparse Key := [(key2353, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6)]

def rawRow19060 : Integer.Sparse Key := [(key2356, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6)]

def rawRow19061 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6)]

def rawRow19062 : Integer.Sparse Key := [(key2356, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6)]

def rawRow19063 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2353, 6), (key2356, 6), (key2356, 6), (key2448, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6)]

def rawRow19064 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2353, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6)]

def rawRow19065 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6)]

def rawRow19066 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2353, 6), (key2356, 6), (key2448, 6), (key2513, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2513, 6)]

def rawRow19067 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2353, 6), (key2513, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2513, 6), (key2451, 6)]

def rawRow19068 : Integer.Sparse Key := [(key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2353, 6), (key2558, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2513, 6)]

def rawRow19069 : Integer.Sparse Key := [(key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2558, 6), (key2353, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6)]

def rawRow19070 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6)]

def rawRow19071 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2513, 6), (key2356, 6), (key2448, 6), (key2353, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2356, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19072 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6)]

def rawRow19073 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2356, 6), (key2451, 6)]

def rawRow19074 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2356, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2356, 6)]

def rawRow19075 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2527, 6), (key2558, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2513, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2448, 6)]

def rawRow19076 : Integer.Sparse Key := [(key2527, 6), (key2527, 6), (key2558, 6), (key2527, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2448, 6)]

def rawRow19077 : Integer.Sparse Key := [(key2527, 6), (key2558, 6), (key2527, 6), (key2527, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2448, 6)]

def rawRow19078 : Integer.Sparse Key := [(key2558, 6), (key2527, 6), (key2527, 6), (key2527, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2513, 6), (key2356, 6), (key2451, 6), (key2356, 6), (key2451, 6), (key2451, 6), (key2356, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2353, 6)]

def rawRow19079 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2498, 6), (key2498, 6)]

def rawRow19080 : Integer.Sparse Key := [(key2372, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2432, 6), (key2498, 6), (key2498, 6)]

def rawRow19081 : Integer.Sparse Key := [(key2372, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2432, 6), (key2498, 6)]

def rawRow19082 : Integer.Sparse Key := [(key2385, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2498, 6), (key2498, 6), (key2498, 6), (key2432, 6)]

def rawRow19083 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2475, 6), (key2475, 6)]

def rawRow19084 : Integer.Sparse Key := [(key2400, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2385, 6), (key2475, 6), (key2475, 6)]

def rawRow19085 : Integer.Sparse Key := [(key2400, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2385, 6), (key2475, 6)]

def rawRow19086 : Integer.Sparse Key := [(key2432, 6), (key2400, 6), (key2400, 6), (key2400, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2475, 6), (key2475, 6), (key2475, 6), (key2385, 6)]

def rawRow19087 : Integer.Sparse Key := [(key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2372, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2498, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6)]

def rawRow19088 : Integer.Sparse Key := [(key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2385, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2432, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6)]

def rawRow19089 : Integer.Sparse Key := [(key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2385, 6), (key2372, 6), (key2372, 6), (key2475, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2400, 6), (key2498, 6), (key2498, 6), (key2432, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6)]

def rawRow19090 : Integer.Sparse Key := [(key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2400, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2475, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6)]

def rawRow19091 : Integer.Sparse Key := [(key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2400, 6), (key2432, 6), (key2400, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2475, 6), (key2385, 6), (key2475, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6)]

def rawRow19092 : Integer.Sparse Key := [(key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2432, 6), (key2400, 6), (key2400, 6), (key2498, 6), (key2466, 6), (key2498, 6), (key2372, 6), (key2466, 6), (key2372, 6), (key2475, 6), (key2475, 6), (key2385, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6)]

def rawRow19093 : Integer.Sparse Key := [(key2466, 6), (key2475, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2372, 6), (key2385, 6), (key2400, 6), (key2475, 6), (key2432, 6), (key2498, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2400, 6), (key2466, 6)]

def rawRow19094 : Integer.Sparse Key := [(key2475, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2385, 6), (key2372, 6), (key2475, 6), (key2400, 6), (key2498, 6), (key2432, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2400, 6)]

def rawRow19095 : Integer.Sparse Key := [(key2466, 6), (key2498, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2400, 6), (key2432, 6), (key2372, 6), (key2498, 6), (key2385, 6), (key2475, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2372, 6), (key2466, 6)]

def rawRow19096 : Integer.Sparse Key := [(key2498, 6), (key2466, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2432, 6), (key2400, 6), (key2498, 6), (key2372, 6), (key2475, 6), (key2385, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2466, 6), (key2372, 6)]

def rawRow19097 : Integer.Sparse Key := [(key2475, 6), (key2498, 6), (key2466, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2466, 6), (key2475, 6), (key2498, 6), (key2385, 6), (key2432, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2372, 6), (key2400, 6), (key2466, 6), (key2466, 6), (key2372, 6), (key2400, 6)]

def rawRow19098 : Integer.Sparse Key := [(key2498, 6), (key2475, 6), (key2466, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2466, 6), (key2498, 6), (key2475, 6), (key2432, 6), (key2385, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2400, 6), (key2372, 6), (key2466, 6), (key2466, 6), (key2400, 6), (key2372, 6)]

def rawRow19099 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 24), (key1102, 24), (key1102, 24)]

def rawRow19100 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1024, 24), (key1102, 24), (key1102, 24)]

def rawRow19101 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1102, 24), (key1024, 24), (key1102, 24)]

def rawRow19102 : Integer.Sparse Key := [(key989, 24), (key1102, 24), (key1102, 24), (key1102, 24), (key1024, 24)]

def rawRow19103 : Integer.Sparse Key := [(key1024, 24), (key989, 24), (key1102, 24), (key1102, 24), (key1102, 24)]

def rawRow19104 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key989, 24), (key1102, 24), (key1102, 24)]

def rawRow19105 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key1102, 24), (key989, 24), (key1102, 24)]

def rawRow19106 : Integer.Sparse Key := [(key1024, 24), (key1102, 24), (key1102, 24), (key1102, 24), (key989, 24)]

def rawRow19107 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1024, 24), (key1102, 24), (key1102, 24)]

def rawRow19108 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1102, 24), (key1024, 24), (key1102, 24)]

def rawRow19109 : Integer.Sparse Key := [(key1102, 24), (key989, 24), (key1102, 24), (key1102, 24), (key1024, 24)]

def rawRow19110 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key989, 24), (key1102, 24), (key1102, 24)]

def rawRow19111 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key1102, 24), (key989, 24), (key1102, 24)]

def rawRow19112 : Integer.Sparse Key := [(key1102, 24), (key1024, 24), (key1102, 24), (key1102, 24), (key989, 24)]

def rawRow19113 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key989, 24), (key1024, 24), (key1102, 24)]

def rawRow19114 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key989, 24), (key1102, 24), (key1024, 24)]

def rawRow19115 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1024, 24), (key989, 24), (key1102, 24)]

def rawRow19116 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1024, 24), (key1102, 24), (key989, 24)]

def rawRow19117 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1102, 24), (key989, 24), (key1024, 24)]

def rawRow19118 : Integer.Sparse Key := [(key1102, 24), (key1102, 24), (key1102, 24), (key1024, 24), (key989, 24)]

def rawRow19119 : Integer.Sparse Key := [(key2610, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2635, 2), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2789, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2)]

def rawRow19120 : Integer.Sparse Key := [(key2626, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2)]

def rawRow19121 : Integer.Sparse Key := [(key2626, 2), (key2635, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2721, 2), (key2824, 2)]

def rawRow19122 : Integer.Sparse Key := [(key2635, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2789, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2721, 2)]

def rawRow19123 : Integer.Sparse Key := [(key2665, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2721, 2), (key2610, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2824, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2), (key2855, 2)]

def rawRow19124 : Integer.Sparse Key := [(key2700, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2)]

def rawRow19125 : Integer.Sparse Key := [(key2700, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2635, 2), (key2789, 2)]

def rawRow19126 : Integer.Sparse Key := [(key2721, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2635, 2)]

def rawRow19127 : Integer.Sparse Key := [(key2780, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2865, 2), (key2610, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2635, 2), (key2635, 2), (key2665, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2789, 2), (key2789, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2855, 2), (key2855, 2), (key2721, 2), (key2721, 2), (key2824, 2), (key2824, 2), (key2865, 2), (key2865, 2), (key2610, 2), (key2626, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2780, 2), (key2700, 2), (key2700, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

def rawRow19128 : Integer.Sparse Key := [(key2780, 2), (key2789, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2626, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2626, 2), (key2610, 2), (key2626, 2), (key2780, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2803, 2)]

def rawRow19129 : Integer.Sparse Key := [(key2789, 2), (key2780, 2), (key2780, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2803, 2), (key2853, 2), (key2803, 2), (key2865, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2626, 2), (key2626, 2), (key2855, 2), (key2853, 2), (key2855, 2), (key2700, 2), (key2853, 2), (key2700, 2), (key2865, 2), (key2865, 2), (key2721, 2), (key2635, 2), (key2626, 2), (key2635, 2), (key2610, 2), (key2626, 2), (key2610, 2), (key2789, 2), (key2780, 2), (key2789, 2), (key2665, 2), (key2780, 2), (key2665, 2), (key2855, 2), (key2803, 2), (key2855, 2), (key2700, 2), (key2803, 2), (key2700, 2), (key2865, 2), (key2824, 2), (key2865, 2), (key2721, 2), (key2824, 2), (key2721, 2), (key2626, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2780, 2), (key2665, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2700, 2), (key2803, 2), (key2700, 2)]

def rawRow19130 : Integer.Sparse Key := [(key2803, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2626, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2855, 2), (key2665, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2721, 2), (key2721, 2), (key2610, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2824, 2), (key2824, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2865, 2), (key2865, 2), (key2635, 2), (key2635, 2), (key2789, 2), (key2789, 2), (key2855, 2), (key2855, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2626, 2), (key2626, 2), (key2780, 2), (key2780, 2), (key2853, 2), (key2853, 2)]

def rawRow19131 : Integer.Sparse Key := [(key2803, 2), (key2824, 2), (key2803, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2700, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2780, 2)]

def rawRow19132 : Integer.Sparse Key := [(key2824, 2), (key2803, 2), (key2803, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2855, 2), (key2855, 2), (key2789, 2), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2855, 2), (key2855, 2), (key2635, 2), (key2721, 2), (key2700, 2), (key2721, 2), (key2665, 2), (key2700, 2), (key2665, 2), (key2824, 2), (key2803, 2), (key2824, 2), (key2610, 2), (key2803, 2), (key2610, 2), (key2865, 2), (key2780, 2), (key2865, 2), (key2626, 2), (key2780, 2), (key2626, 2), (key2855, 2), (key2789, 2), (key2855, 2), (key2635, 2), (key2789, 2), (key2635, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2626, 2)]

def rawRow19133 : Integer.Sparse Key := [(key2853, 2), (key2855, 2), (key2865, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2789, 2), (key2803, 2), (key2855, 2), (key2824, 2), (key2865, 2), (key2626, 2), (key2635, 2), (key2700, 2), (key2855, 2), (key2721, 2), (key2865, 2), (key2610, 2), (key2635, 2), (key2665, 2), (key2789, 2), (key2721, 2), (key2824, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2700, 2), (key2803, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2780, 2), (key2700, 2), (key2803, 2)]

def rawRow19134 : Integer.Sparse Key := [(key2855, 2), (key2853, 2), (key2865, 2), (key2789, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2635, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2721, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2789, 2), (key2780, 2), (key2855, 2), (key2803, 2), (key2865, 2), (key2824, 2), (key2635, 2), (key2626, 2), (key2855, 2), (key2700, 2), (key2865, 2), (key2721, 2), (key2635, 2), (key2610, 2), (key2789, 2), (key2665, 2), (key2824, 2), (key2721, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2610, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2700, 2)]

def rawRow19135 : Integer.Sparse Key := [(key2853, 2), (key2865, 2), (key2855, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2803, 2), (key2824, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2700, 2), (key2721, 2), (key2626, 2), (key2865, 2), (key2635, 2), (key2855, 2), (key2665, 2), (key2721, 2), (key2610, 2), (key2824, 2), (key2635, 2), (key2789, 2), (key2665, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2665, 2), (key2700, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2780, 2)]

def rawRow19136 : Integer.Sparse Key := [(key2865, 2), (key2853, 2), (key2855, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2635, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2855, 2), (key2789, 2), (key2721, 2), (key2700, 2), (key2865, 2), (key2626, 2), (key2855, 2), (key2635, 2), (key2721, 2), (key2665, 2), (key2824, 2), (key2610, 2), (key2789, 2), (key2635, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2780, 2), (key2626, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2780, 2), (key2626, 2)]

def rawRow19137 : Integer.Sparse Key := [(key2855, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2789, 2), (key2824, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2865, 2), (key2853, 2), (key2855, 2), (key2865, 2), (key2635, 2), (key2721, 2), (key2626, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2855, 2), (key2865, 2), (key2789, 2), (key2824, 2), (key2780, 2), (key2803, 2), (key2855, 2), (key2865, 2), (key2635, 2), (key2721, 2), (key2626, 2), (key2700, 2), (key2789, 2), (key2824, 2), (key2635, 2), (key2721, 2), (key2610, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2626, 2), (key2700, 2), (key2610, 2), (key2665, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2780, 2), (key2803, 2), (key2626, 2), (key2700, 2), (key2610, 2), (key2665, 2)]

def rawRow19138 : Integer.Sparse Key := [(key2865, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2824, 2), (key2789, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2721, 2), (key2635, 2), (key2700, 2), (key2626, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2865, 2), (key2855, 2), (key2824, 2), (key2789, 2), (key2803, 2), (key2780, 2), (key2865, 2), (key2855, 2), (key2721, 2), (key2635, 2), (key2700, 2), (key2626, 2), (key2824, 2), (key2789, 2), (key2721, 2), (key2635, 2), (key2665, 2), (key2610, 2), (key2803, 2), (key2780, 2), (key2700, 2), (key2626, 2), (key2665, 2), (key2610, 2), (key2853, 2), (key2803, 2), (key2780, 2), (key2853, 2), (key2700, 2), (key2626, 2), (key2803, 2), (key2780, 2), (key2700, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

def rawRow19139 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 24), (key2837, 24), (key2837, 24)]

def rawRow19140 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2760, 24), (key2837, 24), (key2837, 24)]

def rawRow19141 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2837, 24), (key2760, 24), (key2837, 24)]

def rawRow19142 : Integer.Sparse Key := [(key2368, 24), (key2837, 24), (key2837, 24), (key2837, 24), (key2760, 24)]

def rawRow19143 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 24), (key2837, 24), (key2837, 24)]

def rawRow19144 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2581, 24), (key2837, 24), (key2837, 24)]

def rawRow19145 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2837, 24), (key2581, 24), (key2837, 24)]

def rawRow19146 : Integer.Sparse Key := [(key2396, 24), (key2837, 24), (key2837, 24), (key2837, 24), (key2581, 24)]

def rawRow19147 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2760, 24), (key2837, 24), (key2837, 24)]

def rawRow19148 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2837, 24), (key2760, 24), (key2837, 24)]

def rawRow19149 : Integer.Sparse Key := [(key2462, 24), (key2368, 24), (key2837, 24), (key2837, 24), (key2760, 24)]

def rawRow19150 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2581, 24), (key2837, 24), (key2837, 24)]

def rawRow19151 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2837, 24), (key2581, 24), (key2837, 24)]

def rawRow19152 : Integer.Sparse Key := [(key2462, 24), (key2396, 24), (key2837, 24), (key2837, 24), (key2581, 24)]

def rawRow19153 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2368, 24), (key2760, 24), (key2837, 24)]

def rawRow19154 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2368, 24), (key2837, 24), (key2760, 24)]

def rawRow19155 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2396, 24), (key2581, 24), (key2837, 24)]

def rawRow19156 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2396, 24), (key2837, 24), (key2581, 24)]

def rawRow19157 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2462, 24), (key2368, 24), (key2760, 24)]

def rawRow19158 : Integer.Sparse Key := [(key2462, 24), (key2462, 24), (key2462, 24), (key2396, 24), (key2581, 24)]

def rawRow19159 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key1146, 6), (key1146, 6)]

def rawRow19160 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key1011, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1067, 6), (key1146, 6), (key1146, 6)]

def rawRow19161 : Integer.Sparse Key := [(key995, 6), (key1011, 6), (key995, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1067, 6), (key1146, 6)]

def rawRow19162 : Integer.Sparse Key := [(key1011, 6), (key995, 6), (key995, 6), (key995, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key1146, 6), (key1146, 6), (key1146, 6), (key1067, 6)]

def rawRow19163 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key995, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1119, 6), (key1119, 6)]

def rawRow19164 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1011, 6), (key1119, 6), (key1119, 6)]

def rawRow19165 : Integer.Sparse Key := [(key1030, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1011, 6), (key1119, 6)]

def rawRow19166 : Integer.Sparse Key := [(key1067, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1119, 6), (key1119, 6), (key1119, 6), (key1011, 6)]

def rawRow19167 : Integer.Sparse Key := [(key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key995, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key1146, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6)]

def rawRow19168 : Integer.Sparse Key := [(key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1011, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key1067, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6)]

def rawRow19169 : Integer.Sparse Key := [(key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1011, 6), (key995, 6), (key995, 6), (key1119, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key1030, 6), (key1146, 6), (key1146, 6), (key1067, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6)]

def rawRow19170 : Integer.Sparse Key := [(key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key995, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1119, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6)]

def rawRow19171 : Integer.Sparse Key := [(key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1146, 6), (key995, 6), (key1108, 6), (key1119, 6), (key1011, 6), (key1119, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6)]

def rawRow19172 : Integer.Sparse Key := [(key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1146, 6), (key1108, 6), (key1146, 6), (key995, 6), (key1108, 6), (key995, 6), (key1119, 6), (key1119, 6), (key1011, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6)]

def rawRow19173 : Integer.Sparse Key := [(key1108, 6), (key1119, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key995, 6), (key1011, 6), (key1030, 6), (key1119, 6), (key1067, 6), (key1146, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1030, 6), (key1108, 6)]

def rawRow19174 : Integer.Sparse Key := [(key1119, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1011, 6), (key995, 6), (key1119, 6), (key1030, 6), (key1146, 6), (key1067, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1030, 6)]

def rawRow19175 : Integer.Sparse Key := [(key1108, 6), (key1146, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1030, 6), (key1067, 6), (key995, 6), (key1146, 6), (key1011, 6), (key1119, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key995, 6), (key1108, 6)]

def rawRow19176 : Integer.Sparse Key := [(key1146, 6), (key1108, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1067, 6), (key1030, 6), (key1146, 6), (key995, 6), (key1119, 6), (key1011, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1108, 6), (key1030, 6), (key1108, 6), (key995, 6)]

def rawRow19177 : Integer.Sparse Key := [(key1119, 6), (key1146, 6), (key1108, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key1108, 6), (key1119, 6), (key1146, 6), (key1011, 6), (key1067, 6), (key995, 6), (key1030, 6), (key1108, 6), (key995, 6), (key1030, 6), (key1108, 6), (key1108, 6), (key995, 6), (key1030, 6)]

def rawRow19178 : Integer.Sparse Key := [(key1146, 6), (key1119, 6), (key1108, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1108, 6), (key1146, 6), (key1119, 6), (key1067, 6), (key1011, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1030, 6), (key995, 6), (key1108, 6), (key1108, 6), (key1030, 6), (key995, 6)]

def rawRow19179 : Integer.Sparse Key := [(key2377, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2389, 4), (key2389, 4), (key2405, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2518, 4)]

def rawRow19180 : Integer.Sparse Key := [(key2377, 4), (key2389, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2502, 4)]

def rawRow19181 : Integer.Sparse Key := [(key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2436, 4), (key2502, 4)]

def rawRow19182 : Integer.Sparse Key := [(key2389, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2405, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2436, 4)]

def rawRow19183 : Integer.Sparse Key := [(key2405, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2436, 4), (key2436, 4), (key2377, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2518, 4)]

def rawRow19184 : Integer.Sparse Key := [(key2405, 4), (key2436, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2479, 4)]

def rawRow19185 : Integer.Sparse Key := [(key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2389, 4), (key2479, 4)]

def rawRow19186 : Integer.Sparse Key := [(key2436, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2377, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2389, 4)]

def rawRow19187 : Integer.Sparse Key := [(key2471, 4), (key2479, 4), (key2479, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2377, 4), (key2389, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2502, 4), (key2502, 4), (key2518, 4), (key2518, 4), (key2377, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2405, 4), (key2471, 4), (key2471, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2502, 4)]

def rawRow19188 : Integer.Sparse Key := [(key2479, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2502, 4), (key2389, 4), (key2377, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2389, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2436, 4), (key2502, 4)]

def rawRow19189 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2471, 4), (key2518, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2405, 4), (key2518, 4), (key2502, 4), (key2518, 4), (key2436, 4), (key2502, 4), (key2436, 4), (key2389, 4), (key2377, 4), (key2377, 4), (key2479, 4), (key2471, 4), (key2479, 4), (key2405, 4), (key2471, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2436, 4)]

def rawRow19190 : Integer.Sparse Key := [(key2471, 4), (key2502, 4), (key2502, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2405, 4), (key2436, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2389, 4), (key2479, 4), (key2479, 4), (key2518, 4), (key2518, 4), (key2405, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2377, 4), (key2471, 4), (key2471, 4), (key2502, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2479, 4)]

def rawRow19191 : Integer.Sparse Key := [(key2502, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2479, 4), (key2436, 4), (key2405, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2436, 4), (key2405, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2479, 4), (key2389, 4), (key2479, 4)]

def rawRow19192 : Integer.Sparse Key := [(key2502, 4), (key2502, 4), (key2471, 4), (key2518, 4), (key2479, 4), (key2479, 4), (key2436, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2502, 4), (key2377, 4), (key2518, 4), (key2479, 4), (key2518, 4), (key2389, 4), (key2479, 4), (key2389, 4), (key2436, 4), (key2405, 4), (key2405, 4), (key2502, 4), (key2471, 4), (key2502, 4), (key2377, 4), (key2471, 4), (key2377, 4), (key2479, 4), (key2479, 4), (key2389, 4)]

def rawRow19193 : Integer.Sparse Key := [(key2479, 4), (key2502, 4), (key2518, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2518, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2377, 4), (key2389, 4), (key2405, 4), (key2479, 4), (key2436, 4), (key2502, 4), (key2377, 4), (key2405, 4), (key2471, 4)]

def rawRow19194 : Integer.Sparse Key := [(key2479, 4), (key2518, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2502, 4), (key2389, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2405, 4), (key2502, 4), (key2436, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2389, 4), (key2377, 4), (key2479, 4), (key2405, 4), (key2502, 4), (key2436, 4), (key2377, 4), (key2471, 4), (key2405, 4)]

def rawRow19195 : Integer.Sparse Key := [(key2502, 4), (key2479, 4), (key2518, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2518, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2405, 4), (key2436, 4), (key2377, 4), (key2502, 4), (key2389, 4), (key2479, 4), (key2405, 4), (key2377, 4), (key2471, 4)]

def rawRow19196 : Integer.Sparse Key := [(key2502, 4), (key2518, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2479, 4), (key2436, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2377, 4), (key2479, 4), (key2389, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2436, 4), (key2405, 4), (key2502, 4), (key2377, 4), (key2479, 4), (key2389, 4), (key2405, 4), (key2471, 4), (key2377, 4)]

def rawRow19197 : Integer.Sparse Key := [(key2518, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2518, 4), (key2479, 4), (key2502, 4), (key2518, 4), (key2389, 4), (key2436, 4), (key2479, 4), (key2502, 4), (key2389, 4), (key2436, 4), (key2377, 4), (key2405, 4), (key2479, 4), (key2502, 4), (key2471, 4), (key2479, 4), (key2502, 4), (key2389, 4), (key2436, 4), (key2377, 4), (key2405, 4), (key2471, 4), (key2377, 4), (key2405, 4)]

def rawRow19198 : Integer.Sparse Key := [(key2518, 4), (key2502, 4), (key2479, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2518, 4), (key2502, 4), (key2479, 4), (key2518, 4), (key2436, 4), (key2389, 4), (key2502, 4), (key2479, 4), (key2436, 4), (key2389, 4), (key2405, 4), (key2377, 4), (key2502, 4), (key2479, 4), (key2471, 4), (key2502, 4), (key2479, 4), (key2436, 4), (key2389, 4), (key2405, 4), (key2377, 4), (key2471, 4), (key2405, 4), (key2377, 4)]

def rawRow19199 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2497, 6), (key2497, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19200 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2431, 6), (key2497, 6), (key2497, 6)]

def rawRow19201 : Integer.Sparse Key := [(key2369, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2431, 6), (key2497, 6)]

def rawRow19202 : Integer.Sparse Key := [(key2384, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2497, 6), (key2497, 6), (key2497, 6), (key2431, 6)]

def rawRow19203 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2474, 6), (key2474, 6)]

def rawRow19204 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2384, 6), (key2474, 6), (key2474, 6)]

def rawRow19205 : Integer.Sparse Key := [(key2397, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2384, 6), (key2474, 6)]

def rawRow19206 : Integer.Sparse Key := [(key2431, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2474, 6), (key2474, 6), (key2474, 6), (key2384, 6)]

def rawRow19207 : Integer.Sparse Key := [(key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2497, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6)]

def rawRow19208 : Integer.Sparse Key := [(key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2431, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6)]

def rawRow19209 : Integer.Sparse Key := [(key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2474, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2397, 6), (key2497, 6), (key2497, 6), (key2431, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6)]

def rawRow19210 : Integer.Sparse Key := [(key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2474, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6)]

def rawRow19211 : Integer.Sparse Key := [(key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2384, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6)]

def rawRow19212 : Integer.Sparse Key := [(key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2497, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2369, 6), (key2474, 6), (key2474, 6), (key2384, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6)]

def rawRow19213 : Integer.Sparse Key := [(key2463, 6), (key2474, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2397, 6), (key2463, 6)]

def rawRow19214 : Integer.Sparse Key := [(key2474, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2384, 6), (key2369, 6), (key2474, 6), (key2397, 6), (key2497, 6), (key2431, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2397, 6)]

def rawRow19215 : Integer.Sparse Key := [(key2463, 6), (key2497, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2369, 6), (key2463, 6)]

def rawRow19216 : Integer.Sparse Key := [(key2497, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2431, 6), (key2397, 6), (key2497, 6), (key2369, 6), (key2474, 6), (key2384, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2369, 6)]

def rawRow19217 : Integer.Sparse Key := [(key2474, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2384, 6), (key2431, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2397, 6)]

def rawRow19218 : Integer.Sparse Key := [(key2497, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2431, 6), (key2384, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2369, 6)]

def rawRow19219 : Integer.Sparse Key := [(key2606, 6), (key2622, 6), (key2622, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2776, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6)]

def rawRow19220 : Integer.Sparse Key := [(key2622, 6), (key2606, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6)]

def rawRow19221 : Integer.Sparse Key := [(key2622, 6), (key2622, 6), (key2606, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2776, 6), (key2799, 6)]

def rawRow19222 : Integer.Sparse Key := [(key2622, 6), (key2622, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2849, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2776, 6)]

def rawRow19223 : Integer.Sparse Key := [(key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2622, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6)]

def rawRow19224 : Integer.Sparse Key := [(key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6)]

def rawRow19225 : Integer.Sparse Key := [(key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2622, 6), (key2696, 6)]

def rawRow19226 : Integer.Sparse Key := [(key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2622, 6)]

def rawRow19227 : Integer.Sparse Key := [(key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2606, 6), (key2622, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6)]

def rawRow19228 : Integer.Sparse Key := [(key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2606, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2776, 6), (key2799, 6)]

def rawRow19229 : Integer.Sparse Key := [(key2776, 6), (key2849, 6), (key2849, 6), (key2799, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2776, 6)]

def rawRow19230 : Integer.Sparse Key := [(key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6)]

def rawRow19231 : Integer.Sparse Key := [(key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2622, 6), (key2696, 6)]

def rawRow19232 : Integer.Sparse Key := [(key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2622, 6)]

def rawRow19233 : Integer.Sparse Key := [(key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2606, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2776, 6), (key2799, 6)]

def rawRow19234 : Integer.Sparse Key := [(key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2776, 6)]

def rawRow19235 : Integer.Sparse Key := [(key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2661, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2622, 6), (key2696, 6)]

def rawRow19236 : Integer.Sparse Key := [(key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2606, 6), (key2696, 6), (key2622, 6)]

def rawRow19237 : Integer.Sparse Key := [(key2849, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2776, 6), (key2799, 6), (key2622, 6), (key2696, 6), (key2606, 6), (key2661, 6)]

def rawRow19238 : Integer.Sparse Key := [(key2849, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2799, 6), (key2776, 6), (key2696, 6), (key2622, 6), (key2661, 6), (key2606, 6)]

def rawRow19239 : Integer.Sparse Key := [(key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6)]

def rawRow19240 : Integer.Sparse Key := [(key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6)]

def rawRow19241 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6)]

def rawRow19242 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6)]

def rawRow19243 : Integer.Sparse Key := [(key1884, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1850, 6), (key1850, 6)]

def rawRow19245 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key685, 24), (key692, 24), (key685, 24)]

def rawRow19246 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key692, 24), (key685, 24), (key685, 24)]

def rawRow19247 : Integer.Sparse Key := [(key685, 24), (key692, 24), (key685, 24), (key685, 24), (key685, 24)]

def rawRow19248 : Integer.Sparse Key := [(key692, 24), (key685, 24), (key685, 24), (key685, 24), (key685, 24)]

def rawRow19249 : Integer.Sparse Key := [(key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1877, 2), (key1867, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1877, 2)]

def rawRow19250 : Integer.Sparse Key := [(key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1867, 2)]

def rawRow19251 : Integer.Sparse Key := [(key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2)]

def rawRow19252 : Integer.Sparse Key := [(key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2)]

def rawRow19253 : Integer.Sparse Key := [(key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2)]

def rawRow19254 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1957, 24), (key1957, 24), (key1969, 24)]

def rawRow19255 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1957, 24), (key1969, 24), (key1957, 24)]

def rawRow19256 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1969, 24), (key1957, 24), (key1957, 24)]

def rawRow19257 : Integer.Sparse Key := [(key1957, 24), (key1969, 24), (key1957, 24), (key1957, 24), (key1957, 24)]

def rawRow19258 : Integer.Sparse Key := [(key1969, 24), (key1957, 24), (key1957, 24), (key1957, 24), (key1957, 24)]

def rawRow19259 : Integer.Sparse Key := [(key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key617, 6), (key645, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6)]

def rawRow19260 : Integer.Sparse Key := [(key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6)]

def rawRow19261 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6)]

def rawRow19262 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6)]

def rawRow19263 : Integer.Sparse Key := [(key645, 6), (key645, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key617, 6), (key617, 6)]

def rawRow19264 : Integer.Sparse Key := [(key1851, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow19265 : Integer.Sparse Key := [(key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow19266 : Integer.Sparse Key := [(key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow19267 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19268 : Integer.Sparse Key := [(key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19269 : Integer.Sparse Key := [(key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6)]

def rawRow19270 : Integer.Sparse Key := [(key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6)]

def rawRow19271 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6)]

def rawRow19272 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6)]

def rawRow19273 : Integer.Sparse Key := [(key1953, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1932, 6), (key1932, 6)]

def rawRow19274 : Integer.Sparse Key := [(key1958, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1966, 6), (key1960, 6), (key1966, 6)]

def rawRow19275 : Integer.Sparse Key := [(key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1966, 6), (key1960, 6)]

def rawRow19276 : Integer.Sparse Key := [(key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6)]

def rawRow19277 : Integer.Sparse Key := [(key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

def rawRow19278 : Integer.Sparse Key := [(key1966, 6), (key1966, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

def rawRow19279 : Integer.Sparse Key := [(key288, 24), (key289, 24), (key289, 24), (key289, 24), (key289, 24)]

def rawRow19280 : Integer.Sparse Key := [(key289, 24), (key288, 24), (key289, 24), (key289, 24), (key289, 24)]

def rawRow19281 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key288, 24), (key289, 24), (key289, 24)]

def rawRow19282 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key289, 24), (key288, 24), (key289, 24)]

def rawRow19283 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key289, 24), (key289, 24), (key288, 24)]

def rawRow19284 : Integer.Sparse Key := [(key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2491, 6)]

def rawRow19285 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2491, 6)]

def rawRow19286 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2491, 6), (key2423, 6)]

def rawRow19287 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6)]

def rawRow19288 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6)]

def rawRow19289 : Integer.Sparse Key := [(key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6)]

def rawRow19290 : Integer.Sparse Key := [(key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2416, 6), (key2416, 6), (key2416, 6), (key2489, 6)]

def rawRow19291 : Integer.Sparse Key := [(key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6)]

def rawRow19292 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6)]

def rawRow19293 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6), (key2416, 6)]

def rawRow19294 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1045, 24), (key1131, 24), (key1131, 24)]

def rawRow19295 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1131, 24), (key1045, 24), (key1131, 24)]

def rawRow19296 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1131, 24), (key1131, 24), (key1045, 24)]

def rawRow19297 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1045, 24), (key1045, 24), (key1131, 24)]

def rawRow19298 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1045, 24), (key1131, 24), (key1045, 24)]

def rawRow19299 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1131, 24), (key1045, 24), (key1045, 24)]

def rawRow19300 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1045, 24), (key1045, 24), (key1131, 24)]

def rawRow19301 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1045, 24), (key1131, 24), (key1045, 24)]

def rawRow19302 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1131, 24), (key1045, 24), (key1045, 24)]

def rawRow19303 : Integer.Sparse Key := [(key1131, 24), (key1131, 24), (key1045, 24), (key1045, 24), (key1045, 24)]

def rawRow19304 : Integer.Sparse Key := [(key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2712, 2), (key2712, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2863, 2), (key2688, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2863, 2)]

def rawRow19305 : Integer.Sparse Key := [(key2681, 2), (key2688, 2), (key2681, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2817, 2)]

def rawRow19306 : Integer.Sparse Key := [(key2688, 2), (key2681, 2), (key2681, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2712, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2)]

def rawRow19307 : Integer.Sparse Key := [(key2712, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2688, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2817, 2)]

def rawRow19308 : Integer.Sparse Key := [(key2714, 2), (key2712, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2714, 2)]

def rawRow19309 : Integer.Sparse Key := [(key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2)]

def rawRow19310 : Integer.Sparse Key := [(key2815, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2815, 2)]

def rawRow19311 : Integer.Sparse Key := [(key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2815, 2), (key2712, 2)]

def rawRow19312 : Integer.Sparse Key := [(key2817, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2)]

def rawRow19313 : Integer.Sparse Key := [(key2863, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2712, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2)]

def rawRow19314 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3031, 24), (key3118, 24), (key3118, 24)]

def rawRow19315 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3118, 24), (key3031, 24), (key3118, 24)]

def rawRow19316 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3118, 24), (key3118, 24), (key3031, 24)]

def rawRow19317 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3031, 24), (key3031, 24), (key3118, 24)]

def rawRow19318 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3031, 24), (key3118, 24), (key3031, 24)]

def rawRow19319 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3118, 24), (key3031, 24), (key3031, 24)]

def rawRow19320 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3031, 24), (key3031, 24), (key3118, 24)]

def rawRow19321 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3031, 24), (key3118, 24), (key3031, 24)]

def rawRow19322 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3118, 24), (key3031, 24), (key3031, 24)]

def rawRow19323 : Integer.Sparse Key := [(key2485, 24), (key2485, 24), (key2412, 24), (key3031, 24), (key3031, 24)]

def rawRow19324 : Integer.Sparse Key := [(key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1138, 6)]

def rawRow19325 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1138, 6)]

def rawRow19326 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1138, 6), (key1058, 6)]

def rawRow19327 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19328 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6)]

def rawRow19329 : Integer.Sparse Key := [(key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6)]

def rawRow19330 : Integer.Sparse Key := [(key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1050, 6), (key1050, 6), (key1050, 6), (key1136, 6)]

def rawRow19331 : Integer.Sparse Key := [(key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6)]

def rawRow19332 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6)]

def rawRow19333 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1050, 6), (key1050, 6)]

def rawRow19334 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2504, 4)]

def rawRow19335 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2438, 4), (key2504, 4)]

def rawRow19336 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2420, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2504, 4), (key2438, 4)]

def rawRow19337 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2420, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2495, 4)]

def rawRow19338 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2495, 4), (key2427, 4)]

def rawRow19339 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2504, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2427, 4)]

def rawRow19340 : Integer.Sparse Key := [(key2495, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2504, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4)]

def rawRow19341 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2495, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2438, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2504, 4), (key2438, 4), (key2427, 4), (key2420, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2427, 4)]

def rawRow19342 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2427, 4), (key2427, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2495, 4), (key2427, 4), (key2427, 4)]

def rawRow19343 : Integer.Sparse Key := [(key2504, 4), (key2504, 4), (key2504, 4), (key2495, 4), (key2495, 4), (key2495, 4), (key2504, 4), (key2504, 4), (key2504, 4), (key2438, 4), (key2438, 4), (key2438, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2495, 4), (key2495, 4), (key2495, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2427, 4), (key2420, 4), (key2420, 4), (key2420, 4)]

def rawRow19344 : Integer.Sparse Key := [(key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2490, 6)]

def rawRow19345 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2490, 6)]

def rawRow19346 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2490, 6), (key2422, 6)]

def rawRow19347 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6)]

def rawRow19348 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6)]

def rawRow19349 : Integer.Sparse Key := [(key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6)]

def rawRow19350 : Integer.Sparse Key := [(key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2413, 6), (key2413, 6), (key2413, 6), (key2486, 6)]

def rawRow19351 : Integer.Sparse Key := [(key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2490, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6)]

def rawRow19352 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6)]

def rawRow19353 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2413, 6), (key2486, 6), (key2413, 6), (key2413, 6), (key2413, 6)]

def rawRow19354 : Integer.Sparse Key := [(key2677, 6), (key2677, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3122, 6)]

def rawRow19355 : Integer.Sparse Key := [(key2677, 6), (key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3045, 6), (key3059, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3122, 6), (key3059, 6), (key3094, 6)]

def rawRow19356 : Integer.Sparse Key := [(key2677, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3045, 6), (key3122, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3094, 6), (key3059, 6)]

def rawRow19357 : Integer.Sparse Key := [(key2708, 6), (key2677, 6), (key2677, 6), (key2708, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3122, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3094, 6)]

def rawRow19358 : Integer.Sparse Key := [(key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key2811, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3122, 6), (key3094, 6), (key3059, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6)]

def rawRow19359 : Integer.Sparse Key := [(key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2811, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3122, 6), (key3094, 6), (key3094, 6), (key3122, 6), (key3059, 6), (key3059, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3045, 6)]

def rawRow19360 : Integer.Sparse Key := [(key2811, 6), (key2811, 6), (key2811, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2861, 6), (key2677, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3059, 6), (key3094, 6)]

def rawRow19361 : Integer.Sparse Key := [(key2811, 6), (key2811, 6), (key2861, 6), (key2811, 6), (key2708, 6), (key2708, 6), (key2861, 6), (key2708, 6), (key2677, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key3094, 6), (key3045, 6), (key3059, 6), (key3045, 6), (key3094, 6), (key3045, 6), (key3094, 6), (key3059, 6)]

def rawRow19362 : Integer.Sparse Key := [(key2811, 6), (key2861, 6), (key2811, 6), (key2811, 6), (key2708, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6), (key3059, 6), (key3059, 6), (key3045, 6), (key3045, 6)]

def rawRow19363 : Integer.Sparse Key := [(key2861, 6), (key2811, 6), (key2811, 6), (key2811, 6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2811, 6), (key2811, 6), (key2811, 6), (key2708, 6), (key2708, 6), (key2708, 6), (key2677, 6), (key2677, 6), (key2677, 6), (key3045, 6), (key3045, 6), (key3045, 6)]

def rawRow19364 : Integer.Sparse Key := [(key1962, 24), (key1962, 24), (key1964, 24), (key1964, 24), (key1964, 24)]

def rawRow19365 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1962, 24), (key1964, 24), (key1964, 24)]

def rawRow19366 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1962, 24), (key1964, 24), (key1964, 24)]

def rawRow19367 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1964, 24), (key1962, 24), (key1964, 24)]

def rawRow19368 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1964, 24), (key1962, 24), (key1964, 24)]

def rawRow19369 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1962, 24), (key1962, 24), (key1964, 24)]

def rawRow19370 : Integer.Sparse Key := [(key1962, 24), (key1964, 24), (key1964, 24), (key1964, 24), (key1962, 24)]

def rawRow19371 : Integer.Sparse Key := [(key1964, 24), (key1962, 24), (key1964, 24), (key1964, 24), (key1962, 24)]

def rawRow19372 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1962, 24), (key1964, 24), (key1962, 24)]

def rawRow19373 : Integer.Sparse Key := [(key1964, 24), (key1964, 24), (key1964, 24), (key1962, 24), (key1962, 24)]

def rawRow19374 : Integer.Sparse Key := [(key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12)]

def rawRow19375 : Integer.Sparse Key := [(key3084, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12)]

def rawRow19376 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3079, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12)]

def rawRow19377 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3099, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3084, 12)]

def rawRow19378 : Integer.Sparse Key := [(key3084, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12)]

def rawRow19379 : Integer.Sparse Key := [(key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12)]

def rawRow19380 : Integer.Sparse Key := [(key3084, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3079, 12), (key3084, 12), (key3084, 12), (key3084, 12)]

def rawRow19381 : Integer.Sparse Key := [(key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3099, 12), (key3084, 12), (key3079, 12), (key3084, 12), (key3084, 12)]

def rawRow19382 : Integer.Sparse Key := [(key3099, 12), (key3084, 12), (key3084, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12), (key3084, 12)]

def rawRow19383 : Integer.Sparse Key := [(key3099, 12), (key3099, 12), (key3099, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3084, 12), (key3079, 12)]

def rawRow19384 : Integer.Sparse Key := [(key1273, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6)]

def rawRow19385 : Integer.Sparse Key := [(key1278, 6), (key1273, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6)]

def rawRow19386 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1273, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6)]

def rawRow19387 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6)]

def rawRow19388 : Integer.Sparse Key := [(key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1273, 6), (key1278, 6), (key1278, 6), (key1696, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6)]

def rawRow19389 : Integer.Sparse Key := [(key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1273, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6)]

def rawRow19390 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1278, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6)]

def rawRow19391 : Integer.Sparse Key := [(key1696, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1273, 6), (key1278, 6), (key1696, 6), (key1751, 6), (key1933, 6), (key1953, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6)]

def rawRow19392 : Integer.Sparse Key := [(key1701, 6), (key1696, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1278, 6), (key1273, 6), (key1751, 6), (key1696, 6), (key1953, 6), (key1933, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6)]

def rawRow19393 : Integer.Sparse Key := [(key1696, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1933, 6), (key1273, 6), (key1953, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6)]

def rawRow19394 : Integer.Sparse Key := [(key1933, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1953, 6), (key1273, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6)]

def rawRow19395 : Integer.Sparse Key := [(key1701, 6), (key1933, 6), (key1696, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6)]

def rawRow19396 : Integer.Sparse Key := [(key1933, 6), (key1701, 6), (key1696, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1953, 6), (key1751, 6), (key1933, 6), (key1278, 6), (key1696, 6), (key1273, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6)]

def rawRow19397 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1933, 6), (key1696, 6), (key1751, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1696, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6)]

def rawRow19398 : Integer.Sparse Key := [(key1701, 6), (key1933, 6), (key1701, 6), (key1696, 6), (key1751, 6), (key1953, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1273, 6), (key1696, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6)]

def rawRow19399 : Integer.Sparse Key := [(key1933, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1953, 6), (key1751, 6), (key1751, 6), (key1933, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1696, 6), (key1696, 6), (key1273, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6)]

def rawRow19400 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1751, 6), (key1953, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1273, 6), (key1696, 6), (key1696, 6), (key1696, 6)]

def rawRow19401 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1953, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1696, 6), (key1273, 6), (key1696, 6), (key1696, 6)]

def rawRow19402 : Integer.Sparse Key := [(key1751, 6), (key1953, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1696, 6), (key1696, 6), (key1273, 6), (key1696, 6)]

def rawRow19403 : Integer.Sparse Key := [(key1953, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1933, 6), (key1701, 6), (key1701, 6), (key1933, 6), (key1701, 6), (key1933, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1696, 6), (key1696, 6), (key1696, 6), (key1273, 6)]

def rawRow19404 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key494, 24), (key494, 24), (key548, 24)]

def rawRow19405 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key494, 24), (key548, 24), (key494, 24)]

def rawRow19406 : Integer.Sparse Key := [(key222, 24), (key494, 24), (key548, 24), (key494, 24), (key494, 24)]

def rawRow19407 : Integer.Sparse Key := [(key222, 24), (key548, 24), (key494, 24), (key494, 24), (key494, 24)]

def rawRow19408 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key494, 24), (key494, 24), (key548, 24)]

def rawRow19409 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key494, 24), (key548, 24), (key494, 24)]

def rawRow19410 : Integer.Sparse Key := [(key494, 24), (key222, 24), (key548, 24), (key494, 24), (key494, 24)]

def rawRow19411 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key222, 24), (key494, 24), (key548, 24)]

def rawRow19412 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key222, 24), (key548, 24), (key494, 24)]

def rawRow19413 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key494, 24), (key222, 24), (key548, 24)]

def rawRow19414 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key494, 24), (key548, 24), (key222, 24)]

def rawRow19415 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key548, 24), (key222, 24), (key494, 24)]

def rawRow19416 : Integer.Sparse Key := [(key494, 24), (key494, 24), (key548, 24), (key494, 24), (key222, 24)]

def rawRow19417 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key222, 24), (key494, 24), (key494, 24)]

def rawRow19418 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key494, 24), (key222, 24), (key494, 24)]

def rawRow19419 : Integer.Sparse Key := [(key494, 24), (key548, 24), (key494, 24), (key494, 24), (key222, 24)]

def rawRow19420 : Integer.Sparse Key := [(key548, 24), (key222, 24), (key494, 24), (key494, 24), (key494, 24)]

def rawRow19421 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key222, 24), (key494, 24), (key494, 24)]

def rawRow19422 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key494, 24), (key222, 24), (key494, 24)]

def rawRow19423 : Integer.Sparse Key := [(key548, 24), (key494, 24), (key494, 24), (key494, 24), (key222, 24)]

def rawRow19424 : Integer.Sparse Key := [(key1358, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1484, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1716, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1949, 2)]

def rawRow19425 : Integer.Sparse Key := [(key1364, 2), (key1358, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1949, 2), (key1940, 2)]

def rawRow19426 : Integer.Sparse Key := [(key1364, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2)]

def rawRow19427 : Integer.Sparse Key := [(key1374, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1358, 2), (key1513, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1484, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2)]

def rawRow19428 : Integer.Sparse Key := [(key1484, 2), (key1490, 2), (key1490, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1723, 2), (key1937, 2), (key1937, 2), (key1940, 2), (key1358, 2), (key1364, 2), (key1364, 2), (key1710, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1937, 2), (key1937, 2), (key1949, 2), (key1358, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1374, 2), (key1484, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1513, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1741, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1949, 2), (key1364, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1490, 2), (key1513, 2), (key1716, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1723, 2), (key1741, 2)]

def rawRow19429 : Integer.Sparse Key := [(key1490, 2), (key1484, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1723, 2), (key1710, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1940, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1364, 2), (key1716, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1716, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1374, 2), (key1358, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1513, 2), (key1484, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1741, 2), (key1710, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1937, 2), (key1949, 2), (key1937, 2), (key1949, 2), (key1940, 2), (key1364, 2), (key1374, 2), (key1364, 2), (key1490, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1741, 2), (key1716, 2), (key1741, 2), (key1723, 2)]

def rawRow19430 : Integer.Sparse Key := [(key1490, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1741, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1937, 2), (key1374, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1358, 2), (key1358, 2), (key1513, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1484, 2), (key1484, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1710, 2), (key1710, 2), (key1949, 2), (key1949, 2), (key1940, 2), (key1940, 2), (key1937, 2), (key1937, 2), (key1374, 2), (key1364, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1490, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1716, 2), (key1716, 2)]

def rawRow19431 : Integer.Sparse Key := [(key1710, 2), (key1716, 2), (key1937, 2), (key1484, 2), (key1490, 2), (key1710, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1358, 2), (key1364, 2), (key1710, 2), (key1741, 2), (key1937, 2), (key1949, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1484, 2), (key1490, 2), (key1710, 2), (key1723, 2), (key1937, 2), (key1940, 2), (key1358, 2), (key1364, 2), (key1710, 2), (key1741, 2), (key1937, 2), (key1949, 2), (key1358, 2), (key1374, 2), (key1484, 2), (key1513, 2), (key1940, 2), (key1949, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1513, 2), (key1723, 2), (key1741, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1374, 2), (key1490, 2), (key1513, 2), (key1723, 2), (key1741, 2)]

def rawRow19432 : Integer.Sparse Key := [(key1716, 2), (key1710, 2), (key1937, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1490, 2), (key1484, 2), (key1723, 2), (key1710, 2), (key1940, 2), (key1937, 2), (key1364, 2), (key1358, 2), (key1741, 2), (key1710, 2), (key1949, 2), (key1937, 2), (key1374, 2), (key1358, 2), (key1513, 2), (key1484, 2), (key1949, 2), (key1940, 2), (key1374, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1741, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1374, 2), (key1364, 2), (key1513, 2), (key1490, 2), (key1741, 2), (key1723, 2)]

def rawRow19433 : Integer.Sparse Key := [(key1710, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1937, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1710, 2), (key1937, 2), (key1484, 2), (key1940, 2), (key1490, 2), (key1723, 2), (key1710, 2), (key1937, 2), (key1358, 2), (key1949, 2), (key1364, 2), (key1741, 2), (key1484, 2), (key1940, 2), (key1358, 2), (key1949, 2), (key1374, 2), (key1513, 2), (key1490, 2), (key1723, 2), (key1364, 2), (key1741, 2), (key1374, 2), (key1513, 2), (key1716, 2), (key1490, 2), (key1723, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1490, 2), (key1723, 2), (key1364, 2), (key1741, 2), (key1374, 2), (key1513, 2)]

def rawRow19434 : Integer.Sparse Key := [(key1937, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1710, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1937, 2), (key1710, 2), (key1940, 2), (key1484, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1710, 2), (key1949, 2), (key1358, 2), (key1741, 2), (key1364, 2), (key1940, 2), (key1484, 2), (key1949, 2), (key1358, 2), (key1513, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1741, 2), (key1364, 2), (key1513, 2), (key1374, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1723, 2), (key1490, 2), (key1741, 2), (key1364, 2), (key1513, 2), (key1374, 2)]

def rawRow19435 : Integer.Sparse Key := [(key1716, 2), (key1937, 2), (key1710, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1513, 2), (key1949, 2), (key1374, 2), (key1940, 2), (key1358, 2), (key1484, 2), (key1513, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1364, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1513, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1364, 2), (key1490, 2)]

def rawRow19436 : Integer.Sparse Key := [(key1937, 2), (key1716, 2), (key1710, 2), (key1940, 2), (key1723, 2), (key1937, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1716, 2), (key1710, 2), (key1949, 2), (key1741, 2), (key1937, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1940, 2), (key1723, 2), (key1937, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1949, 2), (key1741, 2), (key1937, 2), (key1364, 2), (key1710, 2), (key1358, 2), (key1949, 2), (key1513, 2), (key1940, 2), (key1374, 2), (key1484, 2), (key1358, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1374, 2), (key1490, 2), (key1364, 2), (key1723, 2), (key1716, 2), (key1490, 2), (key1741, 2), (key1716, 2), (key1364, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1374, 2), (key1490, 2), (key1364, 2)]

def rawRow19437 : Integer.Sparse Key := [(key1723, 2), (key1723, 2), (key1940, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1710, 2), (key1710, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2)]

def rawRow19438 : Integer.Sparse Key := [(key1723, 2), (key1940, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1741, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1490, 2)]

def rawRow19439 : Integer.Sparse Key := [(key1940, 2), (key1723, 2), (key1723, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1710, 2), (key1710, 2), (key1484, 2), (key1949, 2), (key1741, 2), (key1741, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1949, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1513, 2), (key1940, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1374, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1358, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1716, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1364, 2)]

def rawRow19440 : Integer.Sparse Key := [(key1513, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1949, 2), (key1374, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1940, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1937, 2), (key1358, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2), (key1710, 2)]

def rawRow19441 : Integer.Sparse Key := [(key1741, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1937, 2), (key1937, 2), (key1364, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1358, 2), (key1484, 2), (key1484, 2), (key1710, 2), (key1710, 2)]

def rawRow19442 : Integer.Sparse Key := [(key1741, 2), (key1949, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1723, 2), (key1940, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1358, 2), (key1484, 2)]

def rawRow19443 : Integer.Sparse Key := [(key1949, 2), (key1741, 2), (key1741, 2), (key1949, 2), (key1741, 2), (key1949, 2), (key1513, 2), (key1741, 2), (key1513, 2), (key1741, 2), (key1741, 2), (key1513, 2), (key1940, 2), (key1723, 2), (key1723, 2), (key1940, 2), (key1723, 2), (key1940, 2), (key1374, 2), (key1723, 2), (key1374, 2), (key1723, 2), (key1723, 2), (key1374, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1937, 2), (key1716, 2), (key1937, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1937, 2), (key1490, 2), (key1937, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1716, 2), (key1490, 2), (key1716, 2), (key1364, 2), (key1490, 2), (key1364, 2), (key1710, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1710, 2), (key1358, 2), (key1710, 2), (key1484, 2), (key1710, 2), (key1358, 2), (key1484, 2), (key1358, 2)]

def rawRow19444 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1698, 24), (key1698, 24), (key1750, 24)]

def rawRow19445 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1698, 24), (key1750, 24), (key1698, 24)]

def rawRow19446 : Integer.Sparse Key := [(key1275, 24), (key1698, 24), (key1750, 24), (key1698, 24), (key1698, 24)]

def rawRow19447 : Integer.Sparse Key := [(key1275, 24), (key1750, 24), (key1698, 24), (key1698, 24), (key1698, 24)]

def rawRow19448 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1698, 24), (key1698, 24), (key1750, 24)]

def rawRow19449 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1698, 24), (key1750, 24), (key1698, 24)]

def rawRow19450 : Integer.Sparse Key := [(key1698, 24), (key1275, 24), (key1750, 24), (key1698, 24), (key1698, 24)]

def rawRow19451 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1275, 24), (key1698, 24), (key1750, 24)]

def rawRow19452 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1275, 24), (key1750, 24), (key1698, 24)]

def rawRow19453 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1698, 24), (key1275, 24), (key1750, 24)]

def rawRow19454 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1698, 24), (key1750, 24), (key1275, 24)]

def rawRow19455 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1750, 24), (key1275, 24), (key1698, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19456 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1750, 24), (key1698, 24), (key1275, 24)]

def rawRow19457 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1275, 24), (key1698, 24), (key1698, 24)]

def rawRow19458 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1698, 24), (key1275, 24), (key1698, 24)]

def rawRow19459 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1698, 24), (key1698, 24), (key1275, 24)]

def rawRow19460 : Integer.Sparse Key := [(key1750, 24), (key1275, 24), (key1698, 24), (key1698, 24), (key1698, 24)]

def rawRow19461 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1275, 24), (key1698, 24), (key1698, 24)]

def rawRow19462 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1698, 24), (key1275, 24), (key1698, 24)]

def rawRow19463 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1698, 24), (key1698, 24), (key1275, 24)]

def rawRow19464 : Integer.Sparse Key := [(key220, 6), (key225, 6), (key225, 6), (key225, 6), (key492, 6), (key497, 6), (key497, 6), (key492, 6), (key497, 6), (key492, 6), (key551, 6), (key497, 6), (key551, 6), (key497, 6), (key497, 6), (key551, 6), (key664, 6), (key664, 6), (key664, 6), (key681, 6)]

def rawRow19465 : Integer.Sparse Key := [(key225, 6), (key220, 6), (key225, 6), (key225, 6), (key497, 6), (key492, 6), (key497, 6), (key497, 6), (key492, 6), (key551, 6), (key492, 6), (key551, 6), (key497, 6), (key497, 6), (key551, 6), (key497, 6), (key664, 6), (key664, 6), (key681, 6), (key664, 6)]

def rawRow19466 : Integer.Sparse Key := [(key225, 6), (key225, 6), (key220, 6), (key225, 6), (key497, 6), (key497, 6), (key492, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key551, 6), (key497, 6), (key497, 6), (key664, 6), (key681, 6), (key664, 6), (key664, 6)]

def rawRow19467 : Integer.Sparse Key := [(key225, 6), (key225, 6), (key225, 6), (key220, 6), (key551, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key492, 6), (key681, 6), (key664, 6), (key664, 6), (key664, 6)]

def rawRow19468 : Integer.Sparse Key := [(key492, 6), (key497, 6), (key497, 6), (key664, 6), (key220, 6), (key225, 6), (key225, 6), (key492, 6), (key497, 6), (key492, 6), (key551, 6), (key497, 6), (key551, 6), (key664, 6), (key664, 6), (key681, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6)]

def rawRow19469 : Integer.Sparse Key := [(key497, 6), (key492, 6), (key497, 6), (key664, 6), (key225, 6), (key220, 6), (key225, 6), (key497, 6), (key492, 6), (key551, 6), (key492, 6), (key551, 6), (key497, 6), (key664, 6), (key681, 6), (key664, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6)]

def rawRow19470 : Integer.Sparse Key := [(key497, 6), (key497, 6), (key492, 6), (key664, 6), (key225, 6), (key225, 6), (key220, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key681, 6), (key664, 6), (key664, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6)]

def rawRow19471 : Integer.Sparse Key := [(key492, 6), (key497, 6), (key664, 6), (key497, 6), (key492, 6), (key497, 6), (key664, 6), (key220, 6), (key225, 6), (key492, 6), (key551, 6), (key664, 6), (key681, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6), (key551, 6)]

def rawRow19472 : Integer.Sparse Key := [(key497, 6), (key492, 6), (key664, 6), (key497, 6), (key497, 6), (key492, 6), (key664, 6), (key225, 6), (key220, 6), (key551, 6), (key492, 6), (key681, 6), (key664, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6), (key551, 6), (key497, 6)]

def rawRow19473 : Integer.Sparse Key := [(key492, 6), (key664, 6), (key497, 6), (key497, 6), (key492, 6), (key664, 6), (key497, 6), (key492, 6), (key664, 6), (key220, 6), (key681, 6), (key225, 6), (key551, 6), (key497, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6), (key551, 6)]

def rawRow19474 : Integer.Sparse Key := [(key664, 6), (key492, 6), (key497, 6), (key497, 6), (key664, 6), (key492, 6), (key497, 6), (key664, 6), (key492, 6), (key681, 6), (key220, 6), (key551, 6), (key225, 6), (key497, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6), (key225, 6)]

def rawRow19475 : Integer.Sparse Key := [(key497, 6), (key664, 6), (key492, 6), (key497, 6), (key497, 6), (key664, 6), (key492, 6), (key551, 6), (key681, 6), (key225, 6), (key664, 6), (key220, 6), (key492, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6), (key225, 6), (key497, 6)]

def rawRow19476 : Integer.Sparse Key := [(key664, 6), (key497, 6), (key492, 6), (key497, 6), (key664, 6), (key497, 6), (key492, 6), (key681, 6), (key551, 6), (key664, 6), (key225, 6), (key492, 6), (key220, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6), (key225, 6)]

def rawRow19477 : Integer.Sparse Key := [(key497, 6), (key497, 6), (key664, 6), (key492, 6), (key551, 6), (key551, 6), (key681, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key220, 6), (key492, 6), (key492, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6)]

def rawRow19478 : Integer.Sparse Key := [(key497, 6), (key664, 6), (key497, 6), (key492, 6), (key551, 6), (key681, 6), (key551, 6), (key497, 6), (key664, 6), (key225, 6), (key664, 6), (key225, 6), (key497, 6), (key492, 6), (key220, 6), (key492, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6)]

def rawRow19479 : Integer.Sparse Key := [(key664, 6), (key497, 6), (key497, 6), (key492, 6), (key681, 6), (key551, 6), (key551, 6), (key664, 6), (key497, 6), (key664, 6), (key225, 6), (key497, 6), (key225, 6), (key492, 6), (key492, 6), (key220, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6)]

def rawRow19480 : Integer.Sparse Key := [(key551, 6), (key551, 6), (key551, 6), (key681, 6), (key225, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key664, 6), (key220, 6), (key492, 6), (key492, 6), (key492, 6)]

def rawRow19481 : Integer.Sparse Key := [(key551, 6), (key551, 6), (key681, 6), (key551, 6), (key497, 6), (key497, 6), (key664, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key225, 6), (key497, 6), (key497, 6), (key492, 6), (key220, 6), (key492, 6), (key492, 6)]

def rawRow19482 : Integer.Sparse Key := [(key551, 6), (key681, 6), (key551, 6), (key551, 6), (key497, 6), (key664, 6), (key497, 6), (key497, 6), (key664, 6), (key225, 6), (key664, 6), (key225, 6), (key497, 6), (key497, 6), (key225, 6), (key497, 6), (key492, 6), (key492, 6), (key220, 6), (key492, 6)]

def rawRow19483 : Integer.Sparse Key := [(key681, 6), (key551, 6), (key551, 6), (key551, 6), (key664, 6), (key497, 6), (key497, 6), (key664, 6), (key497, 6), (key664, 6), (key225, 6), (key497, 6), (key225, 6), (key497, 6), (key497, 6), (key225, 6), (key492, 6), (key492, 6), (key492, 6), (key220, 6)]

def rawRow19484 : Integer.Sparse Key := [(key1277, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1756, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow19485 : Integer.Sparse Key := [(key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow19486 : Integer.Sparse Key := [(key1283, 4), (key1277, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow19487 : Integer.Sparse Key := [(key1283, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1277, 4), (key1277, 4), (key1756, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19488 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1706, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

def rawRow19489 : Integer.Sparse Key := [(key1700, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

def rawRow19490 : Integer.Sparse Key := [(key1706, 4), (key1700, 4), (key1700, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1283, 4), (key1277, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

def rawRow19491 : Integer.Sparse Key := [(key1700, 4), (key1851, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1855, 4), (key1277, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1756, 4), (key1855, 4), (key1886, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1756, 4), (key1855, 4), (key1886, 4), (key1283, 4), (key1706, 4), (key1756, 4)]

def rawRow19492 : Integer.Sparse Key := [(key1700, 4), (key1855, 4), (key1851, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1851, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1756, 4), (key1706, 4)]

def rawRow19493 : Integer.Sparse Key := [(key1851, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1851, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1700, 4), (key1855, 4), (key1277, 4), (key1886, 4), (key1283, 4), (key1756, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1277, 4), (key1886, 4), (key1283, 4), (key1756, 4), (key1706, 4), (key1283, 4), (key1756, 4)]

def rawRow19494 : Integer.Sparse Key := [(key1851, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1851, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1855, 4), (key1700, 4), (key1886, 4), (key1277, 4), (key1756, 4), (key1283, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1886, 4), (key1277, 4), (key1756, 4), (key1283, 4), (key1706, 4), (key1756, 4), (key1283, 4)]

def rawRow19495 : Integer.Sparse Key := [(key1855, 4), (key1700, 4), (key1851, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1851, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1283, 4), (key1706, 4)]

def rawRow19496 : Integer.Sparse Key := [(key1855, 4), (key1851, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1700, 4), (key1886, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1283, 4), (key1700, 4), (key1277, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1283, 4), (key1700, 4), (key1277, 4), (key1756, 4), (key1706, 4), (key1283, 4)]

def rawRow19497 : Integer.Sparse Key := [(key1706, 4), (key1855, 4), (key1855, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1756, 4), (key1886, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow19498 : Integer.Sparse Key := [(key1855, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow19499 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1706, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1851, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1277, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow19500 : Integer.Sparse Key := [(key1756, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1283, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

def rawRow19501 : Integer.Sparse Key := [(key1756, 4), (key1886, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1700, 4)]

def rawRow19502 : Integer.Sparse Key := [(key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1277, 4), (key1700, 4)]

def rawRow19503 : Integer.Sparse Key := [(key1886, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1283, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1277, 4)]

def rawRow19504 : Integer.Sparse Key := [(key1274, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6)]

def rawRow19505 : Integer.Sparse Key := [(key1278, 6), (key1274, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6)]

def rawRow19506 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1274, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6)]

def rawRow19507 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6)]

def rawRow19508 : Integer.Sparse Key := [(key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1274, 6), (key1278, 6), (key1278, 6), (key1697, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6)]

def rawRow19509 : Integer.Sparse Key := [(key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1274, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6)]

def rawRow19510 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1278, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6)]

def rawRow19511 : Integer.Sparse Key := [(key1697, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1274, 6), (key1278, 6), (key1697, 6), (key1751, 6), (key1852, 6), (key1884, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6)]

def rawRow19512 : Integer.Sparse Key := [(key1701, 6), (key1697, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6)]

def rawRow19513 : Integer.Sparse Key := [(key1697, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1274, 6), (key1884, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6)]

def rawRow19514 : Integer.Sparse Key := [(key1852, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1884, 6), (key1274, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6)]

def rawRow19515 : Integer.Sparse Key := [(key1701, 6), (key1852, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6)]

def rawRow19516 : Integer.Sparse Key := [(key1852, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1884, 6), (key1751, 6), (key1852, 6), (key1278, 6), (key1697, 6), (key1274, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6)]

def rawRow19517 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1751, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1697, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6)]

def rawRow19518 : Integer.Sparse Key := [(key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1884, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1274, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6)]

def rawRow19519 : Integer.Sparse Key := [(key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1884, 6), (key1751, 6), (key1751, 6), (key1852, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1697, 6), (key1697, 6), (key1274, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6)]

def rawRow19520 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1697, 6), (key1697, 6)]

def rawRow19521 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1884, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1274, 6), (key1697, 6), (key1697, 6)]

def rawRow19522 : Integer.Sparse Key := [(key1751, 6), (key1884, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1274, 6), (key1697, 6)]

def rawRow19523 : Integer.Sparse Key := [(key1884, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1274, 6)]

def rawRow19524 : Integer.Sparse Key := [(key1360, 6), (key1360, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1712, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1721, 6), (key1739, 6)]

def rawRow19525 : Integer.Sparse Key := [(key1360, 6), (key1360, 6), (key1372, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1739, 6), (key1721, 6)]

def rawRow19526 : Integer.Sparse Key := [(key1360, 6), (key1372, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6)]

def rawRow19527 : Integer.Sparse Key := [(key1372, 6), (key1360, 6), (key1360, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1739, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6)]

def rawRow19528 : Integer.Sparse Key := [(key1486, 6), (key1712, 6), (key1712, 6), (key1721, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1721, 6), (key1739, 6)]

def rawRow19529 : Integer.Sparse Key := [(key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1372, 6), (key1360, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1739, 6), (key1721, 6)]

def rawRow19530 : Integer.Sparse Key := [(key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1372, 6), (key1360, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6)]

def rawRow19531 : Integer.Sparse Key := [(key1712, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1511, 6), (key1721, 6), (key1739, 6)]

def rawRow19532 : Integer.Sparse Key := [(key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1372, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1739, 6), (key1721, 6)]

def rawRow19533 : Integer.Sparse Key := [(key1712, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1486, 6), (key1721, 6), (key1360, 6), (key1739, 6), (key1372, 6), (key1511, 6)]

def rawRow19534 : Integer.Sparse Key := [(key1712, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1721, 6), (key1486, 6), (key1739, 6), (key1360, 6), (key1511, 6), (key1372, 6)]

def rawRow19535 : Integer.Sparse Key := [(key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1511, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1360, 6), (key1486, 6)]

def rawRow19536 : Integer.Sparse Key := [(key1712, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1372, 6), (key1486, 6), (key1360, 6)]

def rawRow19537 : Integer.Sparse Key := [(key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1511, 6), (key1739, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6)]

def rawRow19538 : Integer.Sparse Key := [(key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1511, 6), (key1739, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1360, 6), (key1486, 6)]

def rawRow19539 : Integer.Sparse Key := [(key1721, 6), (key1712, 6), (key1712, 6), (key1486, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1486, 6), (key1360, 6)]

def rawRow19540 : Integer.Sparse Key := [(key1511, 6), (key1739, 6), (key1739, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1360, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6)]

def rawRow19541 : Integer.Sparse Key := [(key1739, 6), (key1511, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6)]

def rawRow19542 : Integer.Sparse Key := [(key1739, 6), (key1739, 6), (key1511, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1360, 6), (key1486, 6)]

def rawRow19543 : Integer.Sparse Key := [(key1739, 6), (key1739, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1712, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1486, 6), (key1360, 6)]

def rawRow19544 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key515, 24), (key515, 24), (key547, 24)]

def rawRow19545 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key515, 24), (key515, 24), (key547, 24)]

def rawRow19546 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key513, 24), (key515, 24), (key547, 24)]

def rawRow19547 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key515, 24), (key513, 24), (key547, 24)]

def rawRow19548 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key515, 24), (key547, 24), (key515, 24)]

def rawRow19549 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key515, 24), (key547, 24), (key515, 24)]

def rawRow19550 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key513, 24), (key547, 24), (key515, 24)]

def rawRow19551 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key547, 24), (key515, 24), (key515, 24)]

def rawRow19552 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key547, 24), (key515, 24), (key515, 24)]

def rawRow19553 : Integer.Sparse Key := [(key513, 24), (key547, 24), (key515, 24), (key515, 24), (key515, 24)]

def rawRow19554 : Integer.Sparse Key := [(key547, 24), (key513, 24), (key515, 24), (key515, 24), (key515, 24)]

def rawRow19555 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key513, 24), (key515, 24), (key515, 24)]

def rawRow19556 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key513, 24), (key515, 24), (key515, 24)]

def rawRow19557 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key547, 24), (key513, 24), (key515, 24)]

def rawRow19558 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key515, 24), (key513, 24), (key515, 24)]

def rawRow19559 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key515, 24), (key513, 24), (key515, 24)]

def rawRow19560 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key515, 24), (key547, 24), (key513, 24)]

def rawRow19561 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key547, 24), (key515, 24), (key513, 24)]

def rawRow19562 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key515, 24), (key515, 24), (key513, 24)]

def rawRow19563 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key515, 24), (key515, 24), (key513, 24)]

def rawRow19564 : Integer.Sparse Key := [(key1501, 12), (key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1733, 12), (key1735, 12), (key1735, 12), (key1735, 12)]

def rawRow19565 : Integer.Sparse Key := [(key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1733, 12), (key1735, 12), (key1735, 12)]

def rawRow19566 : Integer.Sparse Key := [(key1506, 12), (key1501, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1733, 12), (key1735, 12)]

def rawRow19567 : Integer.Sparse Key := [(key1506, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1735, 12), (key1733, 12)]

def rawRow19568 : Integer.Sparse Key := [(key1501, 12), (key1501, 12), (key1506, 12), (key1733, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1735, 12)]

def rawRow19569 : Integer.Sparse Key := [(key1501, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1733, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1735, 12)]

def rawRow19570 : Integer.Sparse Key := [(key1506, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1733, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1735, 12)]

def rawRow19571 : Integer.Sparse Key := [(key1501, 12), (key1733, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1506, 12)]

def rawRow19572 : Integer.Sparse Key := [(key1501, 12), (key1735, 12), (key1733, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12)]

def rawRow19573 : Integer.Sparse Key := [(key1733, 12), (key1501, 12), (key1735, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1506, 12)]

def rawRow19574 : Integer.Sparse Key := [(key1733, 12), (key1735, 12), (key1501, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1506, 12)]

def rawRow19575 : Integer.Sparse Key := [(key1735, 12), (key1501, 12), (key1733, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12)]

def rawRow19576 : Integer.Sparse Key := [(key1735, 12), (key1733, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1506, 12)]

def rawRow19577 : Integer.Sparse Key := [(key1506, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1733, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1501, 12)]

def rawRow19578 : Integer.Sparse Key := [(key1735, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1733, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1501, 12)]

def rawRow19579 : Integer.Sparse Key := [(key1735, 12), (key1735, 12), (key1506, 12), (key1733, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1501, 12)]

def rawRow19580 : Integer.Sparse Key := [(key1506, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1501, 12), (key1733, 12)]

def rawRow19581 : Integer.Sparse Key := [(key1506, 12), (key1735, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1733, 12), (key1501, 12)]

def rawRow19582 : Integer.Sparse Key := [(key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1733, 12), (key1501, 12), (key1501, 12)]

def rawRow19583 : Integer.Sparse Key := [(key1735, 12), (key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1733, 12), (key1501, 12), (key1501, 12), (key1501, 12)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19584 : Integer.Sparse Key := [(key288, 6), (key289, 6), (key289, 6), (key289, 6), (key513, 6), (key515, 6), (key515, 6), (key513, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key670, 6), (key670, 6), (key670, 6), (key680, 6)]

def rawRow19585 : Integer.Sparse Key := [(key289, 6), (key288, 6), (key289, 6), (key289, 6), (key515, 6), (key513, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key515, 6), (key670, 6), (key670, 6), (key680, 6), (key670, 6)]

def rawRow19586 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key288, 6), (key289, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key670, 6), (key680, 6), (key670, 6), (key670, 6)]

def rawRow19587 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key288, 6), (key547, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key670, 6)]

def rawRow19588 : Integer.Sparse Key := [(key513, 6), (key515, 6), (key515, 6), (key547, 6), (key288, 6), (key289, 6), (key289, 6), (key513, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key547, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6)]

def rawRow19589 : Integer.Sparse Key := [(key515, 6), (key513, 6), (key515, 6), (key547, 6), (key289, 6), (key288, 6), (key289, 6), (key515, 6), (key513, 6), (key547, 6), (key513, 6), (key547, 6), (key515, 6), (key670, 6), (key680, 6), (key670, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6)]

def rawRow19590 : Integer.Sparse Key := [(key515, 6), (key515, 6), (key513, 6), (key547, 6), (key289, 6), (key289, 6), (key288, 6), (key547, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6)]

def rawRow19591 : Integer.Sparse Key := [(key513, 6), (key515, 6), (key547, 6), (key515, 6), (key513, 6), (key515, 6), (key547, 6), (key288, 6), (key289, 6), (key513, 6), (key547, 6), (key670, 6), (key680, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6), (key547, 6)]

def rawRow19592 : Integer.Sparse Key := [(key515, 6), (key513, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key289, 6), (key288, 6), (key547, 6), (key513, 6), (key680, 6), (key670, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6), (key547, 6), (key515, 6)]

def rawRow19593 : Integer.Sparse Key := [(key513, 6), (key547, 6), (key515, 6), (key515, 6), (key513, 6), (key547, 6), (key515, 6), (key513, 6), (key547, 6), (key288, 6), (key680, 6), (key289, 6), (key547, 6), (key515, 6), (key289, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6), (key547, 6)]

def rawRow19594 : Integer.Sparse Key := [(key547, 6), (key513, 6), (key515, 6), (key515, 6), (key547, 6), (key513, 6), (key515, 6), (key547, 6), (key513, 6), (key680, 6), (key288, 6), (key547, 6), (key289, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6)]

def rawRow19595 : Integer.Sparse Key := [(key515, 6), (key547, 6), (key513, 6), (key515, 6), (key515, 6), (key547, 6), (key513, 6), (key670, 6), (key680, 6), (key289, 6), (key547, 6), (key288, 6), (key513, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6)]

def rawRow19596 : Integer.Sparse Key := [(key547, 6), (key515, 6), (key513, 6), (key515, 6), (key547, 6), (key515, 6), (key513, 6), (key680, 6), (key670, 6), (key547, 6), (key289, 6), (key513, 6), (key288, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6), (key547, 6), (key515, 6), (key289, 6)]

def rawRow19597 : Integer.Sparse Key := [(key515, 6), (key515, 6), (key547, 6), (key513, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key288, 6), (key513, 6), (key513, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6)]

def rawRow19598 : Integer.Sparse Key := [(key515, 6), (key547, 6), (key515, 6), (key513, 6), (key670, 6), (key680, 6), (key670, 6), (key515, 6), (key547, 6), (key289, 6), (key547, 6), (key289, 6), (key515, 6), (key513, 6), (key288, 6), (key513, 6), (key547, 6), (key515, 6), (key289, 6), (key515, 6)]

def rawRow19599 : Integer.Sparse Key := [(key547, 6), (key515, 6), (key515, 6), (key513, 6), (key680, 6), (key670, 6), (key670, 6), (key547, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key289, 6), (key513, 6), (key513, 6), (key288, 6), (key547, 6), (key515, 6), (key515, 6), (key289, 6)]

def rawRow19600 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key680, 6), (key289, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key547, 6), (key288, 6), (key513, 6), (key513, 6), (key513, 6)]

def rawRow19601 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key680, 6), (key670, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key289, 6), (key515, 6), (key515, 6), (key547, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key513, 6), (key288, 6), (key513, 6), (key513, 6)]

def rawRow19602 : Integer.Sparse Key := [(key670, 6), (key680, 6), (key670, 6), (key670, 6), (key515, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key289, 6), (key547, 6), (key289, 6), (key515, 6), (key515, 6), (key289, 6), (key515, 6), (key513, 6), (key513, 6), (key288, 6), (key513, 6)]

def rawRow19603 : Integer.Sparse Key := [(key680, 6), (key670, 6), (key670, 6), (key670, 6), (key547, 6), (key515, 6), (key515, 6), (key547, 6), (key515, 6), (key547, 6), (key289, 6), (key515, 6), (key289, 6), (key515, 6), (key515, 6), (key289, 6), (key513, 6), (key513, 6), (key513, 6), (key288, 6)]

def rawRow19604 : Integer.Sparse Key := [(key1251, 6), (key1259, 6), (key1259, 6), (key1271, 6), (key1526, 6), (key1534, 6), (key1534, 6), (key1604, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1640, 6), (key1679, 6), (key1679, 6), (key1693, 6), (key1894, 6), (key1916, 6), (key1916, 6), (key1930, 6)]

def rawRow19605 : Integer.Sparse Key := [(key1259, 6), (key1251, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1526, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1693, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1930, 6), (key1916, 6)]

def rawRow19606 : Integer.Sparse Key := [(key1259, 6), (key1259, 6), (key1251, 6), (key1271, 6), (key1534, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1640, 6), (key1612, 6), (key1612, 6), (key1604, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1679, 6), (key1894, 6), (key1930, 6), (key1916, 6), (key1916, 6)]

def rawRow19607 : Integer.Sparse Key := [(key1251, 6), (key1259, 6), (key1271, 6), (key1259, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1526, 6), (key1534, 6), (key1604, 6), (key1640, 6), (key1679, 6), (key1693, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1916, 6), (key1894, 6), (key1916, 6), (key1930, 6)]

def rawRow19608 : Integer.Sparse Key := [(key1259, 6), (key1251, 6), (key1271, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1894, 6), (key1930, 6), (key1916, 6)]

def rawRow19609 : Integer.Sparse Key := [(key1251, 6), (key1271, 6), (key1259, 6), (key1259, 6), (key1604, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1526, 6), (key1693, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1640, 6), (key1916, 6), (key1916, 6), (key1894, 6), (key1930, 6)]

def rawRow19610 : Integer.Sparse Key := [(key1271, 6), (key1251, 6), (key1259, 6), (key1259, 6), (key1679, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1693, 6), (key1526, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1534, 6), (key1916, 6), (key1916, 6), (key1930, 6), (key1894, 6)]

def rawRow19611 : Integer.Sparse Key := [(key1259, 6), (key1271, 6), (key1251, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1930, 6), (key1894, 6), (key1916, 6)]

def rawRow19612 : Integer.Sparse Key := [(key1271, 6), (key1259, 6), (key1251, 6), (key1259, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1693, 6), (key1640, 6), (key1679, 6), (key1534, 6), (key1604, 6), (key1526, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1916, 6), (key1930, 6), (key1916, 6), (key1894, 6)]

def rawRow19613 : Integer.Sparse Key := [(key1259, 6), (key1259, 6), (key1271, 6), (key1251, 6), (key1640, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1534, 6), (key1612, 6), (key1612, 6), (key1679, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1604, 6), (key1930, 6), (key1894, 6), (key1916, 6), (key1916, 6)]

def rawRow19614 : Integer.Sparse Key := [(key1259, 6), (key1271, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1693, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1526, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1894, 6), (key1916, 6)]

def rawRow19615 : Integer.Sparse Key := [(key1271, 6), (key1259, 6), (key1259, 6), (key1251, 6), (key1693, 6), (key1640, 6), (key1640, 6), (key1679, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1534, 6), (key1604, 6), (key1604, 6), (key1526, 6), (key1930, 6), (key1916, 6), (key1916, 6), (key1894, 6)]

def rawRow19616 : Integer.Sparse Key := [(key1526, 6), (key1534, 6), (key1534, 6), (key1894, 6), (key1251, 6), (key1259, 6), (key1259, 6), (key1604, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1640, 6), (key1916, 6), (key1916, 6), (key1930, 6), (key1271, 6), (key1679, 6), (key1679, 6), (key1693, 6)]

def rawRow19617 : Integer.Sparse Key := [(key1534, 6), (key1526, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1251, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1640, 6), (key1604, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1930, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1693, 6), (key1679, 6)]

def rawRow19618 : Integer.Sparse Key := [(key1534, 6), (key1534, 6), (key1526, 6), (key1894, 6), (key1259, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1640, 6), (key1612, 6), (key1612, 6), (key1604, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1916, 6), (key1271, 6), (key1693, 6), (key1679, 6), (key1679, 6)]

def rawRow19619 : Integer.Sparse Key := [(key1526, 6), (key1534, 6), (key1894, 6), (key1534, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1251, 6), (key1259, 6), (key1604, 6), (key1640, 6), (key1916, 6), (key1930, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1679, 6), (key1271, 6), (key1679, 6), (key1693, 6)]

def rawRow19620 : Integer.Sparse Key := [(key1534, 6), (key1526, 6), (key1894, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1271, 6), (key1693, 6), (key1679, 6)]

def rawRow19621 : Integer.Sparse Key := [(key1526, 6), (key1894, 6), (key1534, 6), (key1534, 6), (key1604, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1251, 6), (key1930, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1640, 6), (key1679, 6), (key1679, 6), (key1271, 6), (key1693, 6)]

def rawRow19622 : Integer.Sparse Key := [(key1894, 6), (key1526, 6), (key1534, 6), (key1534, 6), (key1916, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1930, 6), (key1251, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1259, 6), (key1679, 6), (key1679, 6), (key1693, 6), (key1271, 6)]

def rawRow19623 : Integer.Sparse Key := [(key1534, 6), (key1894, 6), (key1526, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1693, 6), (key1271, 6), (key1679, 6)]

def rawRow19624 : Integer.Sparse Key := [(key1894, 6), (key1534, 6), (key1526, 6), (key1534, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1930, 6), (key1640, 6), (key1916, 6), (key1259, 6), (key1604, 6), (key1251, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1679, 6), (key1693, 6), (key1679, 6), (key1271, 6)]

def rawRow19625 : Integer.Sparse Key := [(key1534, 6), (key1534, 6), (key1894, 6), (key1526, 6), (key1640, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1259, 6), (key1612, 6), (key1612, 6), (key1916, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1604, 6), (key1693, 6), (key1271, 6), (key1679, 6), (key1679, 6)]

def rawRow19626 : Integer.Sparse Key := [(key1534, 6), (key1894, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1930, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1251, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1271, 6), (key1679, 6)]

def rawRow19627 : Integer.Sparse Key := [(key1894, 6), (key1534, 6), (key1534, 6), (key1526, 6), (key1930, 6), (key1640, 6), (key1640, 6), (key1916, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1259, 6), (key1604, 6), (key1604, 6), (key1251, 6), (key1693, 6), (key1679, 6), (key1679, 6), (key1271, 6)]

def rawRow19628 : Integer.Sparse Key := [(key1604, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1251, 6), (key1259, 6), (key1271, 6), (key1526, 6), (key1534, 6), (key1604, 6), (key1640, 6), (key1679, 6), (key1693, 6), (key1894, 6), (key1916, 6), (key1930, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1640, 6)]

def rawRow19629 : Integer.Sparse Key := [(key1612, 6), (key1604, 6), (key1679, 6), (key1916, 6), (key1259, 6), (key1251, 6), (key1271, 6), (key1534, 6), (key1526, 6), (key1640, 6), (key1604, 6), (key1693, 6), (key1679, 6), (key1894, 6), (key1930, 6), (key1916, 6), (key1259, 6), (key1534, 6), (key1640, 6), (key1612, 6)]

def rawRow19630 : Integer.Sparse Key := [(key1604, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1251, 6), (key1271, 6), (key1259, 6), (key1604, 6), (key1679, 6), (key1526, 6), (key1693, 6), (key1534, 6), (key1640, 6), (key1916, 6), (key1894, 6), (key1930, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1640, 6)]

def rawRow19631 : Integer.Sparse Key := [(key1679, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1271, 6), (key1251, 6), (key1259, 6), (key1679, 6), (key1604, 6), (key1693, 6), (key1526, 6), (key1640, 6), (key1534, 6), (key1916, 6), (key1930, 6), (key1894, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1534, 6)]

def rawRow19632 : Integer.Sparse Key := [(key1612, 6), (key1679, 6), (key1604, 6), (key1916, 6), (key1259, 6), (key1271, 6), (key1251, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1930, 6), (key1894, 6), (key1916, 6), (key1259, 6), (key1640, 6), (key1534, 6), (key1612, 6)]

def rawRow19633 : Integer.Sparse Key := [(key1679, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1271, 6), (key1259, 6), (key1251, 6), (key1693, 6), (key1640, 6), (key1679, 6), (key1534, 6), (key1604, 6), (key1526, 6), (key1930, 6), (key1916, 6), (key1894, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1534, 6)]

def rawRow19634 : Integer.Sparse Key := [(key1604, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1526, 6), (key1534, 6), (key1894, 6), (key1251, 6), (key1259, 6), (key1604, 6), (key1640, 6), (key1916, 6), (key1930, 6), (key1271, 6), (key1679, 6), (key1693, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1640, 6)]

def rawRow19635 : Integer.Sparse Key := [(key1612, 6), (key1604, 6), (key1916, 6), (key1679, 6), (key1534, 6), (key1526, 6), (key1894, 6), (key1259, 6), (key1251, 6), (key1640, 6), (key1604, 6), (key1930, 6), (key1916, 6), (key1271, 6), (key1693, 6), (key1679, 6), (key1534, 6), (key1259, 6), (key1640, 6), (key1612, 6)]

def rawRow19636 : Integer.Sparse Key := [(key1604, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1526, 6), (key1894, 6), (key1534, 6), (key1604, 6), (key1916, 6), (key1251, 6), (key1930, 6), (key1259, 6), (key1640, 6), (key1679, 6), (key1271, 6), (key1693, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1640, 6)]

def rawRow19637 : Integer.Sparse Key := [(key1916, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1894, 6), (key1526, 6), (key1534, 6), (key1916, 6), (key1604, 6), (key1930, 6), (key1251, 6), (key1640, 6), (key1259, 6), (key1679, 6), (key1693, 6), (key1271, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1259, 6)]

def rawRow19638 : Integer.Sparse Key := [(key1612, 6), (key1916, 6), (key1604, 6), (key1679, 6), (key1534, 6), (key1894, 6), (key1526, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1693, 6), (key1271, 6), (key1679, 6), (key1534, 6), (key1640, 6), (key1259, 6), (key1612, 6)]

def rawRow19639 : Integer.Sparse Key := [(key1916, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1894, 6), (key1534, 6), (key1526, 6), (key1930, 6), (key1640, 6), (key1916, 6), (key1259, 6), (key1604, 6), (key1251, 6), (key1693, 6), (key1679, 6), (key1271, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1259, 6)]

def rawRow19640 : Integer.Sparse Key := [(key1604, 6), (key1679, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1679, 6), (key1916, 6), (key1251, 6), (key1271, 6), (key1526, 6), (key1693, 6), (key1894, 6), (key1930, 6), (key1259, 6), (key1534, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1534, 6), (key1640, 6)]

def rawRow19641 : Integer.Sparse Key := [(key1679, 6), (key1604, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1916, 6), (key1271, 6), (key1251, 6), (key1693, 6), (key1526, 6), (key1930, 6), (key1894, 6), (key1259, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1640, 6), (key1534, 6)]

def rawRow19642 : Integer.Sparse Key := [(key1604, 6), (key1916, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1916, 6), (key1679, 6), (key1526, 6), (key1894, 6), (key1251, 6), (key1930, 6), (key1271, 6), (key1693, 6), (key1534, 6), (key1259, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1259, 6), (key1640, 6)]

def rawRow19643 : Integer.Sparse Key := [(key1916, 6), (key1604, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1679, 6), (key1894, 6), (key1526, 6), (key1930, 6), (key1251, 6), (key1693, 6), (key1271, 6), (key1534, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1640, 6), (key1259, 6)]

def rawRow19644 : Integer.Sparse Key := [(key1679, 6), (key1916, 6), (key1604, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1604, 6), (key1693, 6), (key1930, 6), (key1271, 6), (key1894, 6), (key1251, 6), (key1526, 6), (key1640, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1640, 6), (key1259, 6), (key1534, 6)]

def rawRow19645 : Integer.Sparse Key := [(key1916, 6), (key1679, 6), (key1604, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1604, 6), (key1930, 6), (key1693, 6), (key1894, 6), (key1271, 6), (key1526, 6), (key1251, 6), (key1640, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1640, 6), (key1534, 6), (key1259, 6)]

def rawRow19646 : Integer.Sparse Key := [(key1612, 6), (key1679, 6), (key1916, 6), (key1604, 6), (key1640, 6), (key1693, 6), (key1930, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1251, 6), (key1526, 6), (key1604, 6), (key1640, 6), (key1259, 6), (key1534, 6), (key1612, 6)]

def rawRow19647 : Integer.Sparse Key := [(key1679, 6), (key1612, 6), (key1916, 6), (key1604, 6), (key1693, 6), (key1640, 6), (key1930, 6), (key1271, 6), (key1259, 6), (key1679, 6), (key1534, 6), (key1916, 6), (key1894, 6), (key1251, 6), (key1604, 6), (key1526, 6), (key1640, 6), (key1259, 6), (key1612, 6), (key1534, 6)]

def rawRow19648 : Integer.Sparse Key := [(key1612, 6), (key1916, 6), (key1679, 6), (key1604, 6), (key1640, 6), (key1930, 6), (key1693, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1526, 6), (key1251, 6), (key1604, 6), (key1640, 6), (key1534, 6), (key1259, 6), (key1612, 6)]

def rawRow19649 : Integer.Sparse Key := [(key1916, 6), (key1612, 6), (key1679, 6), (key1604, 6), (key1930, 6), (key1640, 6), (key1693, 6), (key1894, 6), (key1534, 6), (key1916, 6), (key1259, 6), (key1679, 6), (key1271, 6), (key1526, 6), (key1604, 6), (key1251, 6), (key1640, 6), (key1534, 6), (key1612, 6), (key1259, 6)]

def rawRow19650 : Integer.Sparse Key := [(key1679, 6), (key1916, 6), (key1612, 6), (key1604, 6), (key1693, 6), (key1930, 6), (key1640, 6), (key1679, 6), (key1916, 6), (key1271, 6), (key1894, 6), (key1259, 6), (key1534, 6), (key1604, 6), (key1251, 6), (key1526, 6), (key1640, 6), (key1612, 6), (key1259, 6), (key1534, 6)]

def rawRow19651 : Integer.Sparse Key := [(key1916, 6), (key1679, 6), (key1612, 6), (key1604, 6), (key1930, 6), (key1693, 6), (key1640, 6), (key1916, 6), (key1679, 6), (key1894, 6), (key1271, 6), (key1534, 6), (key1259, 6), (key1604, 6), (key1526, 6), (key1251, 6), (key1640, 6), (key1612, 6), (key1534, 6), (key1259, 6)]

def rawRow19652 : Integer.Sparse Key := [(key1640, 6), (key1640, 6), (key1693, 6), (key1930, 6), (key1259, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1534, 6), (key1612, 6), (key1612, 6), (key1679, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1916, 6), (key1251, 6), (key1526, 6), (key1604, 6), (key1604, 6)]

def rawRow19653 : Integer.Sparse Key := [(key1640, 6), (key1693, 6), (key1640, 6), (key1930, 6), (key1259, 6), (key1271, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1894, 6), (key1916, 6), (key1251, 6), (key1604, 6), (key1526, 6), (key1604, 6)]

def rawRow19654 : Integer.Sparse Key := [(key1693, 6), (key1640, 6), (key1640, 6), (key1930, 6), (key1271, 6), (key1259, 6), (key1259, 6), (key1679, 6), (key1612, 6), (key1679, 6), (key1534, 6), (key1612, 6), (key1534, 6), (key1916, 6), (key1916, 6), (key1894, 6), (key1251, 6), (key1604, 6), (key1604, 6), (key1526, 6)]

def rawRow19655 : Integer.Sparse Key := [(key1640, 6), (key1640, 6), (key1930, 6), (key1693, 6), (key1534, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1259, 6), (key1612, 6), (key1612, 6), (key1916, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1679, 6), (key1526, 6), (key1251, 6), (key1604, 6), (key1604, 6)]

def rawRow19656 : Integer.Sparse Key := [(key1640, 6), (key1930, 6), (key1640, 6), (key1693, 6), (key1534, 6), (key1894, 6), (key1534, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1679, 6), (key1271, 6), (key1679, 6), (key1526, 6), (key1604, 6), (key1251, 6), (key1604, 6)]

def rawRow19657 : Integer.Sparse Key := [(key1930, 6), (key1640, 6), (key1640, 6), (key1693, 6), (key1894, 6), (key1534, 6), (key1534, 6), (key1916, 6), (key1612, 6), (key1916, 6), (key1259, 6), (key1612, 6), (key1259, 6), (key1679, 6), (key1679, 6), (key1271, 6), (key1526, 6), (key1604, 6), (key1604, 6), (key1251, 6)]

def rawRow19658 : Integer.Sparse Key := [(key1640, 6), (key1693, 6), (key1930, 6), (key1640, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1259, 6), (key1271, 6), (key1534, 6), (key1679, 6), (key1894, 6), (key1916, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1604, 6), (key1251, 6), (key1526, 6), (key1604, 6)]

def rawRow19659 : Integer.Sparse Key := [(key1693, 6), (key1640, 6), (key1930, 6), (key1640, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1271, 6), (key1259, 6), (key1679, 6), (key1534, 6), (key1916, 6), (key1894, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1604, 6), (key1251, 6), (key1604, 6), (key1526, 6)]

def rawRow19660 : Integer.Sparse Key := [(key1640, 6), (key1930, 6), (key1693, 6), (key1640, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1534, 6), (key1894, 6), (key1259, 6), (key1916, 6), (key1271, 6), (key1679, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1604, 6), (key1526, 6), (key1251, 6), (key1604, 6)]

def rawRow19661 : Integer.Sparse Key := [(key1930, 6), (key1640, 6), (key1693, 6), (key1640, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1894, 6), (key1534, 6), (key1916, 6), (key1259, 6), (key1679, 6), (key1271, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1604, 6), (key1526, 6), (key1604, 6), (key1251, 6)]

def rawRow19662 : Integer.Sparse Key := [(key1693, 6), (key1930, 6), (key1640, 6), (key1640, 6), (key1679, 6), (key1916, 6), (key1612, 6), (key1679, 6), (key1916, 6), (key1271, 6), (key1894, 6), (key1259, 6), (key1534, 6), (key1612, 6), (key1259, 6), (key1534, 6), (key1604, 6), (key1604, 6), (key1251, 6), (key1526, 6)]

def rawRow19663 : Integer.Sparse Key := [(key1930, 6), (key1693, 6), (key1640, 6), (key1640, 6), (key1916, 6), (key1679, 6), (key1612, 6), (key1916, 6), (key1679, 6), (key1894, 6), (key1271, 6), (key1534, 6), (key1259, 6), (key1612, 6), (key1534, 6), (key1259, 6), (key1604, 6), (key1604, 6), (key1526, 6), (key1251, 6)]

def rawRow19664 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 24), (key428, 24), (key456, 24)]

def rawRow19665 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key428, 24), (key456, 24), (key428, 24)]

def rawRow19666 : Integer.Sparse Key := [(key208, 24), (key377, 24), (key456, 24), (key428, 24), (key428, 24)]

def rawRow19667 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key377, 24), (key428, 24), (key456, 24)]

def rawRow19668 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key377, 24), (key456, 24), (key428, 24)]

def rawRow19669 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key428, 24), (key377, 24), (key456, 24)]

def rawRow19670 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key428, 24), (key456, 24), (key377, 24)]

def rawRow19671 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key456, 24), (key377, 24), (key428, 24)]

def rawRow19672 : Integer.Sparse Key := [(key208, 24), (key428, 24), (key456, 24), (key428, 24), (key377, 24)]

def rawRow19673 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key377, 24), (key428, 24), (key428, 24)]

def rawRow19674 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key428, 24), (key377, 24), (key428, 24)]

def rawRow19675 : Integer.Sparse Key := [(key208, 24), (key456, 24), (key428, 24), (key428, 24), (key377, 24)]

def rawRow19676 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key428, 24), (key428, 24), (key456, 24)]

def rawRow19677 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key428, 24), (key456, 24), (key428, 24)]

def rawRow19678 : Integer.Sparse Key := [(key377, 24), (key208, 24), (key456, 24), (key428, 24), (key428, 24)]

def rawRow19679 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key208, 24), (key428, 24), (key456, 24)]

def rawRow19680 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key208, 24), (key456, 24), (key428, 24)]

def rawRow19681 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key428, 24), (key208, 24), (key456, 24)]

def rawRow19682 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key428, 24), (key456, 24), (key208, 24)]

def rawRow19683 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key456, 24), (key208, 24), (key428, 24)]

def rawRow19684 : Integer.Sparse Key := [(key377, 24), (key428, 24), (key456, 24), (key428, 24), (key208, 24)]

def rawRow19685 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key208, 24), (key428, 24), (key428, 24)]

def rawRow19686 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key428, 24), (key208, 24), (key428, 24)]

def rawRow19687 : Integer.Sparse Key := [(key377, 24), (key456, 24), (key428, 24), (key428, 24), (key208, 24)]

def rawRow19688 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key377, 24), (key428, 24), (key456, 24)]

def rawRow19689 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key377, 24), (key456, 24), (key428, 24)]

def rawRow19690 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key428, 24), (key377, 24), (key456, 24)]

def rawRow19691 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key428, 24), (key456, 24), (key377, 24)]

def rawRow19692 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key456, 24), (key377, 24), (key428, 24)]

def rawRow19693 : Integer.Sparse Key := [(key428, 24), (key208, 24), (key456, 24), (key428, 24), (key377, 24)]

def rawRow19694 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key208, 24), (key428, 24), (key456, 24)]

def rawRow19695 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key208, 24), (key456, 24), (key428, 24)]

def rawRow19696 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key428, 24), (key208, 24), (key456, 24)]

def rawRow19697 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key428, 24), (key456, 24), (key208, 24)]

def rawRow19698 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key456, 24), (key208, 24), (key428, 24)]

def rawRow19699 : Integer.Sparse Key := [(key428, 24), (key377, 24), (key456, 24), (key428, 24), (key208, 24)]

def rawRow19700 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key208, 24), (key377, 24), (key456, 24)]

def rawRow19701 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key208, 24), (key456, 24), (key377, 24)]

def rawRow19702 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key377, 24), (key208, 24), (key456, 24)]

def rawRow19703 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key377, 24), (key456, 24), (key208, 24)]

def rawRow19704 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key456, 24), (key208, 24), (key377, 24)]

def rawRow19705 : Integer.Sparse Key := [(key428, 24), (key428, 24), (key456, 24), (key377, 24), (key208, 24)]

def rawRow19706 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key208, 24), (key377, 24), (key428, 24)]

def rawRow19707 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key208, 24), (key428, 24), (key377, 24)]

def rawRow19708 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key377, 24), (key208, 24), (key428, 24)]

def rawRow19709 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key377, 24), (key428, 24), (key208, 24)]

def rawRow19710 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key428, 24), (key208, 24), (key377, 24)]

def rawRow19711 : Integer.Sparse Key := [(key428, 24), (key456, 24), (key428, 24), (key377, 24), (key208, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19712 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key377, 24), (key428, 24), (key428, 24)]

def rawRow19713 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key428, 24), (key377, 24), (key428, 24)]

def rawRow19714 : Integer.Sparse Key := [(key456, 24), (key208, 24), (key428, 24), (key428, 24), (key377, 24)]

def rawRow19715 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key208, 24), (key428, 24), (key428, 24)]

def rawRow19716 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key428, 24), (key208, 24), (key428, 24)]

def rawRow19717 : Integer.Sparse Key := [(key456, 24), (key377, 24), (key428, 24), (key428, 24), (key208, 24)]

def rawRow19718 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key208, 24), (key377, 24), (key428, 24)]

def rawRow19719 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key208, 24), (key428, 24), (key377, 24)]

def rawRow19720 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key377, 24), (key208, 24), (key428, 24)]

def rawRow19721 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key377, 24), (key428, 24), (key208, 24)]

def rawRow19722 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key428, 24), (key208, 24), (key377, 24)]

def rawRow19723 : Integer.Sparse Key := [(key456, 24), (key428, 24), (key428, 24), (key377, 24), (key208, 24)]

def rawRow19784 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 24), (key1606, 24), (key1636, 24)]

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

def rawRow1904 : Integer.Sparse Key := [(key2353, -2), (key2359, -2), (key2359, -2), (key2359, 6), (key2448, 2), (key2454, 2), (key2454, 2), (key2454, -2), (key2454, -2), (key2515, -2), (key2566, -6), (key2566, 2), (key2566, 2), (key2578, 2)]

def rawRow1905 : Integer.Sparse Key := [(key2359, -2), (key2353, -2), (key2359, -2), (key2359, 6), (key2454, 2), (key2448, 2), (key2454, 2), (key2454, -2), (key2515, -2), (key2454, -2), (key2566, -6), (key2566, 2), (key2578, 2), (key2566, 2)]

def rawRow1906 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2353, -2), (key2359, 6), (key2454, 2), (key2454, 2), (key2448, 2), (key2515, -2), (key2454, -2), (key2454, -2), (key2566, -6), (key2578, 2), (key2566, 2), (key2566, 2)]

def rawRow1908 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2454, -2), (key2515, 6), (key2353, 2), (key2359, 2), (key2359, 2), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, -6), (key2454, 2), (key2454, 2), (key2515, 2)]

def rawRow1909 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2454, -2), (key2515, 6), (key2359, 2), (key2353, 2), (key2359, 2), (key2566, -2), (key2578, -2), (key2566, -2), (key2359, -6), (key2454, 2), (key2515, 2), (key2454, 2)]

def rawRow1910 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2448, -2), (key2515, 6), (key2359, 2), (key2359, 2), (key2353, 2), (key2578, -2), (key2566, -2), (key2566, -2), (key2359, -6), (key2515, 2), (key2454, 2), (key2454, 2)]

def rawRow1911 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2515, -2), (key2448, 6), (key2566, 2), (key2566, 2), (key2578, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2515, -6), (key2359, 2), (key2454, 2), (key2454, 2)]

def rawRow1912 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2454, -2), (key2448, 6), (key2566, 2), (key2578, 2), (key2566, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2515, -6), (key2454, 2), (key2359, 2), (key2454, 2)]

def rawRow1913 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2578, 2), (key2566, 2), (key2566, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2515, -6), (key2454, 2), (key2454, 2), (key2359, 2)]

def rawRow1915 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2578, -2), (key2566, 6), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, -2), (key2454, -2), (key2454, -2), (key2448, -6), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow1916 : Integer.Sparse Key := [(key2566, -2), (key2578, -2), (key2566, -2), (key2566, 6), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, -2), (key2359, -2), (key2454, -2), (key2448, -6), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow1917 : Integer.Sparse Key := [(key2578, -2), (key2566, -2), (key2566, -2), (key2566, 6), (key2515, 2), (key2454, 2), (key2454, 2), (key2454, -2), (key2454, -2), (key2359, -2), (key2448, -6), (key2448, 2), (key2448, 2), (key2353, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1932 : Integer.Sparse Key := [(key1249, -6), (key1249, 2), (key1249, 2), (key1262, 2), (key1524, 6), (key1524, -2), (key1524, -2), (key1762, -2), (key1602, -2), (key1602, -2), (key1645, -2), (key1602, 2), (key1602, 2), (key1803, 2)]

def rawRow1933 : Integer.Sparse Key := [(key1249, -6), (key1249, 2), (key1262, 2), (key1249, 2), (key1524, 6), (key1524, -2), (key1762, -2), (key1524, -2), (key1602, -2), (key1645, -2), (key1602, -2), (key1602, 2), (key1803, 2), (key1602, 2)]

def rawRow1934 : Integer.Sparse Key := [(key1249, -6), (key1262, 2), (key1249, 2), (key1249, 2), (key1524, 6), (key1762, -2), (key1524, -2), (key1524, -2), (key1645, -2), (key1602, -2), (key1602, -2), (key1803, 2), (key1602, 2), (key1602, 2)]

def rawRow1936 : Integer.Sparse Key := [(key1524, -6), (key1602, 2), (key1602, 2), (key1645, 2), (key1249, 6), (key1602, -2), (key1602, -2), (key1803, -2), (key1249, -2), (key1249, -2), (key1262, -2), (key1524, 2), (key1524, 2), (key1762, 2)]

def rawRow1937 : Integer.Sparse Key := [(key1524, -6), (key1602, 2), (key1645, 2), (key1602, 2), (key1249, 6), (key1602, -2), (key1803, -2), (key1602, -2), (key1249, -2), (key1262, -2), (key1249, -2), (key1524, 2), (key1762, 2), (key1524, 2)]

def rawRow1938 : Integer.Sparse Key := [(key1524, -6), (key1645, 2), (key1602, 2), (key1602, 2), (key1249, 6), (key1803, -2), (key1602, -2), (key1602, -2), (key1262, -2), (key1249, -2), (key1249, -2), (key1762, 2), (key1524, 2), (key1524, 2)]

def rawRow1939 : Integer.Sparse Key := [(key1645, -6), (key1524, 2), (key1602, 2), (key1602, 2), (key1803, 6), (key1249, -2), (key1602, -2), (key1602, -2), (key1762, -2), (key1803, -2), (key1803, -2), (key1262, 2), (key1645, 2), (key1645, 2)]

def rawRow1940 : Integer.Sparse Key := [(key1645, -6), (key1602, 2), (key1524, 2), (key1602, 2), (key1803, 6), (key1602, -2), (key1249, -2), (key1602, -2), (key1803, -2), (key1762, -2), (key1803, -2), (key1645, 2), (key1262, 2), (key1645, 2)]

def rawRow1941 : Integer.Sparse Key := [(key1645, -6), (key1602, 2), (key1602, 2), (key1524, 2), (key1803, 6), (key1602, -2), (key1602, -2), (key1249, -2), (key1803, -2), (key1803, -2), (key1762, -2), (key1645, 2), (key1645, 2), (key1262, 2)]

def rawRow1943 : Integer.Sparse Key := [(key1803, -6), (key1762, 2), (key1803, 2), (key1803, 2), (key1645, 6), (key1262, -2), (key1645, -2), (key1645, -2), (key1524, -2), (key1602, -2), (key1602, -2), (key1249, 2), (key1602, 2), (key1602, 2)]

def rawRow1944 : Integer.Sparse Key := [(key1803, -6), (key1803, 2), (key1762, 2), (key1803, 2), (key1645, 6), (key1645, -2), (key1262, -2), (key1645, -2), (key1602, -2), (key1524, -2), (key1602, -2), (key1602, 2), (key1249, 2), (key1602, 2)]

def rawRow1945 : Integer.Sparse Key := [(key1803, -6), (key1803, 2), (key1803, 2), (key1762, 2), (key1645, 6), (key1645, -2), (key1645, -2), (key1262, -2), (key1602, -2), (key1602, -2), (key1524, -2), (key1602, 2), (key1602, 2), (key1249, 2)]

def rawRow1946 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, -1), (key2767, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2930, -1), (key2840, -1), (key2844, -1), (key2840, -1), (key2888, -1), (key2844, -1), (key2888, -1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1)]

def rawRow1947 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, -1), (key2763, -1), (key2930, -1), (key2763, -1), (key2930, -1), (key2767, -1), (key2844, -1), (key2840, -1), (key2888, -1), (key2840, -1), (key2888, -1), (key2844, -1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1)]

def rawRow1948 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, -1), (key2930, -1), (key2767, -1), (key2767, -1), (key2763, -1), (key2763, -1), (key2888, -1), (key2888, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1)]

def rawRow1950 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, -1), (key2844, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2967, -1), (key2584, -1), (key2588, -1), (key2584, -1), (key2599, -1), (key2588, -1), (key2599, -1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1)]

def rawRow1951 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, -1), (key2840, -1), (key2967, -1), (key2840, -1), (key2967, -1), (key2844, -1), (key2588, -1), (key2584, -1), (key2599, -1), (key2584, -1), (key2599, -1), (key2588, -1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1)]

def rawRow1952 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, -1), (key2967, -1), (key2844, -1), (key2844, -1), (key2840, -1), (key2840, -1), (key2599, -1), (key2599, -1), (key2588, -1), (key2588, -1), (key2584, -1), (key2584, -1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1)]

def rawRow1953 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, -1), (key2588, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2930, -1), (key2930, -1), (key2967, -1), (key2967, -1), (key2988, -1), (key2988, -1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1)]

def rawRow1954 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, -1), (key2875, -1), (key2588, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2967, -1), (key2988, -1), (key2930, -1), (key2988, -1), (key2930, -1), (key2967, -1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1)]

def rawRow1955 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, -1), (key2844, -1), (key2875, -1), (key2588, -1), (key2844, -1), (key2588, -1), (key2988, -1), (key2967, -1), (key2988, -1), (key2930, -1), (key2967, -1), (key2930, -1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1)]

def rawRow1957 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, -1), (key2599, -1), (key2888, -1), (key2888, -1), (key2909, -1), (key2909, -1), (key2767, -1), (key2767, -1), (key2844, -1), (key2844, -1), (key2875, -1), (key2875, -1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1)]

def rawRow1958 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, -1), (key2909, -1), (key2599, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2844, -1), (key2875, -1), (key2767, -1), (key2875, -1), (key2767, -1), (key2844, -1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1)]

def rawRow1959 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, -1), (key2888, -1), (key2909, -1), (key2599, -1), (key2888, -1), (key2599, -1), (key2875, -1), (key2844, -1), (key2875, -1), (key2767, -1), (key2844, -1), (key2767, -1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1)]

def rawRow1960 : Integer.Sparse Key := [(key972, -2), (key977, -2), (key977, -2), (key977, 6), (key1086, 2), (key1091, 2), (key1091, 2), (key1091, -2), (key1091, -2), (key1181, -2), (key1162, -6), (key1162, 2), (key1162, 2), (key1218, 2)]

def rawRow1961 : Integer.Sparse Key := [(key977, -2), (key972, -2), (key977, -2), (key977, 6), (key1091, 2), (key1086, 2), (key1091, 2), (key1091, -2), (key1181, -2), (key1091, -2), (key1162, -6), (key1162, 2), (key1218, 2), (key1162, 2)]

def rawRow1962 : Integer.Sparse Key := [(key977, -2), (key977, -2), (key972, -2), (key977, 6), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, -2), (key1091, -2), (key1091, -2), (key1162, -6), (key1218, 2), (key1162, 2), (key1162, 2)]

def rawRow1964 : Integer.Sparse Key := [(key1086, -2), (key1091, -2), (key1091, -2), (key1162, 6), (key972, 2), (key977, 2), (key977, 2), (key1162, -2), (key1162, -2), (key1218, -2), (key977, -6), (key1091, 2), (key1091, 2), (key1181, 2)]

def rawRow1965 : Integer.Sparse Key := [(key1091, -2), (key1086, -2), (key1091, -2), (key1162, 6), (key977, 2), (key972, 2), (key977, 2), (key1162, -2), (key1218, -2), (key1162, -2), (key977, -6), (key1091, 2), (key1181, 2), (key1091, 2)]

def rawRow1966 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1086, -2), (key1162, 6), (key977, 2), (key977, 2), (key972, 2), (key1218, -2), (key1162, -2), (key1162, -2), (key977, -6), (key1181, 2), (key1091, 2), (key1091, 2)]

def rawRow1967 : Integer.Sparse Key := [(key1091, -2), (key1091, -2), (key1162, -2), (key1086, 6), (key1181, 2), (key1181, 2), (key1218, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1181, -6), (key977, 2), (key1091, 2), (key1091, 2)]

def rawRow1968 : Integer.Sparse Key := [(key1091, -2), (key1162, -2), (key1091, -2), (key1086, 6), (key1181, 2), (key1218, 2), (key1181, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1181, -6), (key1091, 2), (key977, 2), (key1091, 2)]

def rawRow1969 : Integer.Sparse Key := [(key1162, -2), (key1091, -2), (key1091, -2), (key1086, 6), (key1218, 2), (key1181, 2), (key1181, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1181, -6), (key1091, 2), (key1091, 2), (key977, 2)]

def rawRow1971 : Integer.Sparse Key := [(key1181, -2), (key1181, -2), (key1218, -2), (key1181, 6), (key1091, 2), (key1091, 2), (key1162, 2), (key977, -2), (key1091, -2), (key1091, -2), (key1086, -6), (key972, 2), (key1086, 2), (key1086, 2)]

def rawRow1972 : Integer.Sparse Key := [(key1181, -2), (key1218, -2), (key1181, -2), (key1181, 6), (key1091, 2), (key1162, 2), (key1091, 2), (key1091, -2), (key977, -2), (key1091, -2), (key1086, -6), (key1086, 2), (key972, 2), (key1086, 2)]

end MUB6.Certificate.GramRows

end OAI
end


