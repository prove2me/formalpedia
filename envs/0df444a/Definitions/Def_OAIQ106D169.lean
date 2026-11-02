-- Prove2me | Definitions.Def_OAIQ106D169
-- name    : OAIQ106D169
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:33:56.988393+00:00
-- url     : https://prove2.me/theorems/3f1ba0fe-f882-4bd6-895c-bac4147fece3
-- title:
--   Definitions bundle OAIQ106D169 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 597 declarations of OpenAI's Lean: 597 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow20298`, `OAI.MUB6.Certificate.GramRows.rawRow20299`, `OAI.MUB6.Certificate.GramRows.rawRow2030`, `OAI.MUB6.Certificate.GramRows.rawRow20300`, `OAI.MUB6.Certificate.GramRows.rawRow20301`, `OAI.MUB6.Certificate.GramRows.rawRow20302`, `OAI.MUB6.Certificate.GramRows.rawRow20303`, `OAI.MUB6.Certificate.GramRows.rawRow20304`, `OAI.MUB6.Certificate.GramRows.rawRow20305`, `OAI.MUB6.Certificate.GramRows.rawRow20306`, `OAI.MUB6.Certificate.GramRows.rawRow20307`, `OAI.MUB6.Certificate.GramRows.rawRow20308`, `OAI.MUB6.Certificate.GramRows.rawRow20309`, `OAI.MUB6.Certificate.GramRows.rawRow2031`, `OAI.MUB6.Certificate.GramRows.rawRow20310`, `OAI.MUB6.Certificate.GramRows.rawRow20311`, `OAI.MUB6.Certificate.GramRows.rawRow20312`, `OAI.MUB6.Certificate.GramRows.rawRow20313`, `OAI.MUB6.Certificate.GramRows.rawRow20314`, `OAI.MUB6.Certificate.GramRows.rawRow20315`, `OAI.MUB6.Certificate.GramRows.rawRow20316`, `OAI.MUB6.Certificate.GramRows.rawRow20317`, `OAI.MUB6.Certificate.GramRows.rawRow20318`, `OAI.MUB6.Certificate.GramRows.rawRow20319`, `OAI.MUB6.Certificate.GramRows.rawRow2032`, `OAI.MUB6.Certificate.GramRows.rawRow20320`, `OAI.MUB6.Certificate.GramRows.rawRow20321`, `OAI.MUB6.Certificate.GramRows.rawRow20322`, `OAI.MUB6.Certificate.GramRows.rawRow20323`, `OAI.MUB6.Certificate.GramRows.rawRow2034`, `OAI.MUB6.Certificate.GramRows.rawRow2035`, `OAI.MUB6.Certificate.GramRows.rawRow2036`, `OAI.MUB6.Certificate.GramRows.rawRow2037`, `OAI.MUB6.Certificate.GramRows.rawRow2038`, `OAI.MUB6.Certificate.GramRows.rawRow2039`, `OAI.MUB6.Certificate.GramRows.rawRow2041`, `OAI.MUB6.Certificate.GramRows.rawRow2042`, `OAI.MUB6.Certificate.GramRows.rawRow2043`, `OAI.MUB6.Certificate.GramRows.rawRow2058`, `OAI.MUB6.Certificate.GramRows.rawRow2059` and 557 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block182`, `MutuallyUnbiased_GramRows_Block39`, `MutuallyUnbiased_GramRows_Block4`, `MutuallyUnbiased_GramRows_Block40`, `MutuallyUnbiased_GramRows_Block41`, `MutuallyUnbiased_GramRows_Block42`, `MutuallyUnbiased_GramRows_Block43`, `MutuallyUnbiased_GramRows_Block44`, `MutuallyUnbiased_GramRows_Block45`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block5`, `MutuallyUnbiased_GramRows_Block6`, `MutuallyUnbiased_GramRows_Block82`.
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval11_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_11`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D088
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
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

def rawRow21 : Integer.Sparse Key := [(key388, -1), (key385, -1), (key397, 2), (key409, 1), (key406, 1), (key469, -1), (key442, -1), (key418, -2), (key475, 1), (key450, 1), (key251, 1), (key248, 1), (key260, -2), (key319, -1), (key316, -1), (key595, 1), (key442, 1), (key328, 2), (key601, -1), (key450, -1), (key239, -1), (key236, -1), (key271, 1), (key267, 1), (key305, 1), (key302, 1), (key340, -1), (key335, -1), (key572, -1), (key568, -1), (key583, 1), (key578, 1), (key239, 2), (key260, -1), (key251, -1), (key305, -2), (key328, 1), (key319, 1), (key397, 1), (key388, 1), (key418, -1), (key409, -1)]

def rawRow22 : Integer.Sparse Key := [(key388, -1), (key397, -1), (key385, 2), (key467, 1), (key469, 1), (key406, -1), (key435, -1), (key475, -2), (key418, 1), (key450, 1), (key251, 1), (key260, 1), (key248, -2), (key593, -1), (key595, -1), (key316, 1), (key435, 1), (key601, 2), (key328, -1), (key450, -1), (key267, -1), (key271, -1), (key236, 1), (key248, 1), (key328, 1), (key340, 1), (key302, -1), (key316, -1), (key583, -1), (key601, -1), (key572, 1), (key595, 1), (key260, 2), (key239, -1), (key251, -1), (key328, -2), (key305, 1), (key319, 1), (key418, 1), (key450, 1), (key397, -1), (key442, -1)]

def rawRow23 : Integer.Sparse Key := [(key397, -1), (key388, -1), (key385, 2), (key469, 1), (key467, 1), (key435, -1), (key406, -1), (key475, -2), (key450, 1), (key418, 1), (key260, 1), (key251, 1), (key248, -2), (key595, -1), (key593, -1), (key435, 1), (key316, 1), (key601, 2), (key450, -1), (key328, -1), (key271, -1), (key267, -1), (key248, 1), (key236, 1), (key340, 1), (key328, 1), (key316, -1), (key302, -1), (key601, -1), (key583, -1), (key595, 1), (key572, 1), (key260, 2), (key251, -1), (key239, -1), (key328, -2), (key319, 1), (key305, 1), (key450, 1), (key418, 1), (key442, -1), (key397, -1)]

def rawRow24 : Integer.Sparse Key := [(key406, -1), (key409, -1), (key418, 2), (key385, 1), (key388, 1), (key450, -1), (key475, -1), (key397, -2), (key442, 1), (key469, 1), (key316, 1), (key319, 1), (key328, -2), (key248, -1), (key251, -1), (key450, 1), (key601, 1), (key260, 2), (key442, -1), (key595, -1), (key302, -1), (key305, -1), (key328, 1), (key340, 1), (key236, 1), (key239, 1), (key578, -1), (key583, -1), (key267, -1), (key271, -1), (key335, 1), (key340, 1), (key305, 2), (key388, -1), (key397, -1), (key239, -2), (key409, 1), (key418, 1), (key251, 1), (key260, 1), (key319, -1), (key328, -1)]

def rawRow25 : Integer.Sparse Key := [(key409, -1), (key406, -1), (key418, 2), (key388, 1), (key385, 1), (key475, -1), (key450, -1), (key397, -2), (key469, 1), (key442, 1), (key319, 1), (key316, 1), (key328, -2), (key251, -1), (key248, -1), (key601, 1), (key450, 1), (key260, 2), (key595, -1), (key442, -1), (key305, -1), (key302, -1), (key340, 1), (key328, 1), (key239, 1), (key236, 1), (key583, -1), (key578, -1), (key271, -1), (key267, -1), (key340, 1), (key335, 1), (key305, 2), (key397, -1), (key388, -1), (key239, -2), (key418, 1), (key409, 1), (key260, 1), (key251, 1), (key328, -1), (key319, -1)]

def rawRow28 : Integer.Sparse Key := [(key467, -1), (key469, -1), (key475, 2), (key388, 1), (key397, 1), (key418, -1), (key450, -1), (key385, -2), (key406, 1), (key435, 1), (key593, 1), (key595, 1), (key601, -2), (key251, -1), (key260, -1), (key328, 1), (key450, 1), (key248, 2), (key316, -1), (key435, -1), (key568, -1), (key572, -1), (key583, 1), (key601, 1), (key267, 1), (key271, 1), (key340, -1), (key475, -1), (key236, -1), (key248, -1), (key302, 1), (key316, 1), (key328, 2), (key418, -1), (key450, -1), (key260, -2), (key397, 1), (key442, 1), (key239, 1), (key251, 1), (key305, -1), (key319, -1)]

def rawRow29 : Integer.Sparse Key := [(key469, -1), (key467, -1), (key475, 2), (key397, 1), (key388, 1), (key450, -1), (key418, -1), (key385, -2), (key435, 1), (key406, 1), (key595, 1), (key593, 1), (key601, -2), (key260, -1), (key251, -1), (key450, 1), (key328, 1), (key248, 2), (key435, -1), (key316, -1), (key572, -1), (key568, -1), (key601, 1), (key583, 1), (key271, 1), (key267, 1), (key475, -1), (key340, -1), (key248, -1), (key236, -1), (key316, 1), (key302, 1), (key328, 2), (key450, -1), (key418, -1), (key260, -2), (key442, 1), (key397, 1), (key251, 1), (key239, 1), (key319, -1), (key305, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20298 : Integer.Sparse Key := [(key411, 2), (key421, 2), (key406, 2), (key487, 2), (key489, 2), (key390, 2), (key453, 2), (key385, 2), (key435, 2), (key488, 2), (key400, 2), (key445, 2), (key321, 2), (key331, 2), (key316, 2), (key660, 2), (key662, 2), (key253, 2), (key453, 2), (key248, 2), (key435, 2), (key661, 2), (key263, 2), (key445, 2), (key346, 2), (key347, 2), (key307, 2), (key331, 2), (key302, 2), (key316, 2), (key657, 2), (key658, 2), (key241, 2), (key421, 2), (key236, 2), (key406, 2), (key331, 2), (key662, 2), (key263, 2), (key661, 2), (key248, 2), (key316, 2), (key347, 2), (key489, 2), (key278, 2), (key488, 2), (key277, 2), (key346, 2), (key400, 2), (key307, 2), (key390, 2), (key421, 2), (key241, 2), (key411, 2), (key331, 2), (key453, 2), (key263, 2), (key445, 2), (key253, 2), (key321, 2)]

def rawRow20299 : Integer.Sparse Key := [(key421, 2), (key411, 2), (key406, 2), (key489, 2), (key487, 2), (key453, 2), (key390, 2), (key435, 2), (key385, 2), (key488, 2), (key445, 2), (key400, 2), (key331, 2), (key321, 2), (key316, 2), (key662, 2), (key660, 2), (key453, 2), (key253, 2), (key435, 2), (key248, 2), (key661, 2), (key445, 2), (key263, 2), (key347, 2), (key346, 2), (key331, 2), (key307, 2), (key316, 2), (key302, 2), (key658, 2), (key657, 2), (key421, 2), (key241, 2), (key406, 2), (key236, 2), (key662, 2), (key331, 2), (key661, 2), (key263, 2), (key316, 2), (key248, 2), (key489, 2), (key347, 2), (key488, 2), (key278, 2), (key346, 2), (key277, 2), (key400, 2), (key390, 2), (key307, 2), (key421, 2), (key411, 2), (key241, 2), (key453, 2), (key331, 2), (key445, 2), (key263, 2), (key321, 2), (key253, 2)]

def rawRow20300 : Integer.Sparse Key := [(key435, 2), (key445, 2), (key453, 2), (key385, 2), (key400, 2), (key406, 2), (key488, 2), (key421, 2), (key489, 2), (key390, 2), (key411, 2), (key487, 2), (key435, 2), (key445, 2), (key453, 2), (key248, 2), (key263, 2), (key316, 2), (key661, 2), (key331, 2), (key662, 2), (key253, 2), (key321, 2), (key660, 2), (key385, 2), (key400, 2), (key406, 2), (key488, 2), (key421, 2), (key489, 2), (key248, 2), (key263, 2), (key316, 2), (key661, 2), (key331, 2), (key662, 2), (key236, 2), (key278, 2), (key302, 2), (key347, 2), (key656, 2), (key658, 2), (key241, 2), (key263, 2), (key307, 2), (key331, 2), (key400, 2), (key421, 2), (key321, 2), (key411, 2), (key445, 2), (key253, 2), (key390, 2), (key453, 2), (key241, 2), (key263, 2), (key307, 2), (key331, 2), (key400, 2), (key421, 2)]

def rawRow20301 : Integer.Sparse Key := [(key445, 2), (key435, 2), (key453, 2), (key400, 2), (key385, 2), (key488, 2), (key406, 2), (key489, 2), (key421, 2), (key390, 2), (key487, 2), (key411, 2), (key445, 2), (key435, 2), (key453, 2), (key263, 2), (key248, 2), (key661, 2), (key316, 2), (key662, 2), (key331, 2), (key253, 2), (key660, 2), (key321, 2), (key400, 2), (key385, 2), (key488, 2), (key406, 2), (key489, 2), (key421, 2), (key263, 2), (key248, 2), (key661, 2), (key316, 2), (key662, 2), (key331, 2), (key278, 2), (key236, 2), (key347, 2), (key302, 2), (key658, 2), (key656, 2), (key263, 2), (key241, 2), (key331, 2), (key307, 2), (key421, 2), (key400, 2), (key321, 2), (key445, 2), (key411, 2), (key253, 2), (key453, 2), (key390, 2), (key263, 2), (key241, 2), (key331, 2), (key307, 2), (key421, 2), (key400, 2)]

def rawRow20302 : Integer.Sparse Key := [(key435, 2), (key453, 2), (key445, 2), (key406, 2), (key421, 2), (key385, 2), (key489, 2), (key400, 2), (key488, 2), (key411, 2), (key390, 2), (key487, 2), (key435, 2), (key453, 2), (key445, 2), (key316, 2), (key331, 2), (key248, 2), (key662, 2), (key263, 2), (key661, 2), (key321, 2), (key253, 2), (key660, 2), (key406, 2), (key421, 2), (key385, 2), (key489, 2), (key400, 2), (key488, 2), (key316, 2), (key331, 2), (key248, 2), (key662, 2), (key263, 2), (key661, 2), (key302, 2), (key347, 2), (key236, 2), (key658, 2), (key278, 2), (key347, 2), (key307, 2), (key400, 2), (key241, 2), (key421, 2), (key263, 2), (key331, 2), (key411, 2), (key321, 2), (key445, 2), (key390, 2), (key253, 2), (key453, 2), (key307, 2), (key400, 2), (key241, 2), (key421, 2), (key263, 2), (key331, 2)]

def rawRow20303 : Integer.Sparse Key := [(key453, 2), (key435, 2), (key445, 2), (key421, 2), (key406, 2), (key489, 2), (key385, 2), (key488, 2), (key400, 2), (key411, 2), (key487, 2), (key390, 2), (key453, 2), (key435, 2), (key445, 2), (key331, 2), (key316, 2), (key662, 2), (key248, 2), (key661, 2), (key263, 2), (key321, 2), (key660, 2), (key253, 2), (key421, 2), (key406, 2), (key489, 2), (key385, 2), (key488, 2), (key400, 2), (key331, 2), (key316, 2), (key662, 2), (key248, 2), (key661, 2), (key263, 2), (key347, 2), (key302, 2), (key658, 2), (key236, 2), (key347, 2), (key278, 2), (key400, 2), (key307, 2), (key421, 2), (key241, 2), (key331, 2), (key263, 2), (key411, 2), (key445, 2), (key321, 2), (key390, 2), (key453, 2), (key253, 2), (key400, 2), (key307, 2), (key421, 2), (key241, 2), (key331, 2), (key263, 2)]

def rawRow20304 : Integer.Sparse Key := [(key445, 2), (key453, 2), (key435, 2), (key488, 2), (key489, 2), (key400, 2), (key421, 2), (key385, 2), (key406, 2), (key487, 2), (key390, 2), (key411, 2), (key445, 2), (key453, 2), (key435, 2), (key661, 2), (key662, 2), (key263, 2), (key331, 2), (key248, 2), (key316, 2), (key660, 2), (key253, 2), (key321, 2), (key488, 2), (key489, 2), (key400, 2), (key421, 2), (key385, 2), (key406, 2), (key661, 2), (key662, 2), (key263, 2), (key331, 2), (key248, 2), (key316, 2), (key656, 2), (key658, 2), (key278, 2), (key347, 2), (key236, 2), (key302, 2), (key331, 2), (key421, 2), (key263, 2), (key400, 2), (key241, 2), (key307, 2), (key445, 2), (key321, 2), (key411, 2), (key453, 2), (key253, 2), (key390, 2), (key331, 2), (key421, 2), (key263, 2), (key400, 2), (key241, 2), (key307, 2)]

def rawRow20305 : Integer.Sparse Key := [(key453, 2), (key445, 2), (key435, 2), (key489, 2), (key488, 2), (key421, 2), (key400, 2), (key406, 2), (key385, 2), (key487, 2), (key411, 2), (key390, 2), (key453, 2), (key445, 2), (key435, 2), (key662, 2), (key661, 2), (key331, 2), (key263, 2), (key316, 2), (key248, 2), (key660, 2), (key321, 2), (key253, 2), (key489, 2), (key488, 2), (key421, 2), (key400, 2), (key406, 2), (key385, 2), (key662, 2), (key661, 2), (key331, 2), (key263, 2), (key316, 2), (key248, 2), (key658, 2), (key656, 2), (key347, 2), (key278, 2), (key302, 2), (key236, 2), (key421, 2), (key331, 2), (key400, 2), (key263, 2), (key307, 2), (key241, 2), (key445, 2), (key411, 2), (key321, 2), (key453, 2), (key390, 2), (key253, 2), (key421, 2), (key331, 2), (key400, 2), (key263, 2), (key307, 2), (key241, 2)]

def rawRow20306 : Integer.Sparse Key := [(key487, 2), (key488, 2), (key489, 2), (key390, 2), (key400, 2), (key411, 2), (key445, 2), (key421, 2), (key453, 2), (key385, 2), (key406, 2), (key435, 2), (key660, 2), (key661, 2), (key662, 2), (key253, 2), (key263, 2), (key321, 2), (key445, 2), (key331, 2), (key453, 2), (key248, 2), (key316, 2), (key435, 2), (key655, 2), (key656, 2), (key657, 2), (key661, 2), (key658, 2), (key662, 2), (key277, 2), (key278, 2), (key346, 2), (key488, 2), (key347, 2), (key489, 2), (key241, 2), (key263, 2), (key307, 2), (key400, 2), (key331, 2), (key421, 2), (key236, 2), (key248, 2), (key302, 2), (key316, 2), (key385, 2), (key406, 2), (key331, 2), (key421, 2), (key453, 2), (key263, 2), (key400, 2), (key445, 2), (key241, 2), (key253, 2), (key307, 2), (key321, 2), (key390, 2), (key411, 2)]

def rawRow20307 : Integer.Sparse Key := [(key488, 2), (key487, 2), (key489, 2), (key400, 2), (key390, 2), (key445, 2), (key411, 2), (key453, 2), (key421, 2), (key385, 2), (key435, 2), (key406, 2), (key661, 2), (key660, 2), (key662, 2), (key263, 2), (key253, 2), (key445, 2), (key321, 2), (key453, 2), (key331, 2), (key248, 2), (key435, 2), (key316, 2), (key656, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key658, 2), (key278, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key347, 2), (key263, 2), (key241, 2), (key400, 2), (key307, 2), (key421, 2), (key331, 2), (key248, 2), (key236, 2), (key316, 2), (key302, 2), (key406, 2), (key385, 2), (key331, 2), (key453, 2), (key421, 2), (key263, 2), (key445, 2), (key400, 2), (key253, 2), (key241, 2), (key321, 2), (key307, 2), (key411, 2), (key390, 2)]

def rawRow20308 : Integer.Sparse Key := [(key487, 2), (key489, 2), (key488, 2), (key411, 2), (key421, 2), (key390, 2), (key453, 2), (key400, 2), (key445, 2), (key406, 2), (key385, 2), (key435, 2), (key660, 2), (key662, 2), (key661, 2), (key321, 2), (key331, 2), (key253, 2), (key453, 2), (key263, 2), (key445, 2), (key316, 2), (key248, 2), (key435, 2), (key657, 2), (key658, 2), (key655, 2), (key662, 2), (key656, 2), (key661, 2), (key346, 2), (key347, 2), (key277, 2), (key489, 2), (key278, 2), (key488, 2), (key307, 2), (key331, 2), (key241, 2), (key421, 2), (key263, 2), (key400, 2), (key302, 2), (key316, 2), (key236, 2), (key406, 2), (key248, 2), (key316, 2), (key421, 2), (key331, 2), (key453, 2), (key400, 2), (key263, 2), (key445, 2), (key307, 2), (key390, 2), (key241, 2), (key411, 2), (key253, 2), (key321, 2)]

def rawRow20309 : Integer.Sparse Key := [(key489, 2), (key487, 2), (key488, 2), (key421, 2), (key411, 2), (key453, 2), (key390, 2), (key445, 2), (key400, 2), (key406, 2), (key435, 2), (key385, 2), (key662, 2), (key660, 2), (key661, 2), (key331, 2), (key321, 2), (key453, 2), (key253, 2), (key445, 2), (key263, 2), (key316, 2), (key435, 2), (key248, 2), (key658, 2), (key657, 2), (key662, 2), (key655, 2), (key661, 2), (key656, 2), (key347, 2), (key346, 2), (key489, 2), (key277, 2), (key488, 2), (key278, 2), (key331, 2), (key307, 2), (key421, 2), (key241, 2), (key400, 2), (key263, 2), (key316, 2), (key302, 2), (key406, 2), (key236, 2), (key316, 2), (key248, 2), (key421, 2), (key453, 2), (key331, 2), (key400, 2), (key445, 2), (key263, 2), (key390, 2), (key307, 2), (key411, 2), (key241, 2), (key321, 2), (key253, 2)]

def rawRow20310 : Integer.Sparse Key := [(key488, 2), (key489, 2), (key487, 2), (key445, 2), (key453, 2), (key400, 2), (key421, 2), (key390, 2), (key411, 2), (key435, 2), (key385, 2), (key406, 2), (key661, 2), (key662, 2), (key660, 2), (key445, 2), (key453, 2), (key263, 2), (key331, 2), (key253, 2), (key321, 2), (key435, 2), (key248, 2), (key316, 2), (key661, 2), (key662, 2), (key656, 2), (key658, 2), (key655, 2), (key657, 2), (key488, 2), (key489, 2), (key278, 2), (key347, 2), (key277, 2), (key346, 2), (key400, 2), (key421, 2), (key263, 2), (key331, 2), (key241, 2), (key307, 2), (key385, 2), (key406, 2), (key248, 2), (key316, 2), (key236, 2), (key302, 2), (key453, 2), (key331, 2), (key421, 2), (key445, 2), (key263, 2), (key400, 2), (key321, 2), (key411, 2), (key253, 2), (key390, 2), (key241, 2), (key307, 2)]

def rawRow20311 : Integer.Sparse Key := [(key489, 2), (key488, 2), (key487, 2), (key453, 2), (key445, 2), (key421, 2), (key400, 2), (key411, 2), (key390, 2), (key435, 2), (key406, 2), (key385, 2), (key662, 2), (key661, 2), (key660, 2), (key453, 2), (key445, 2), (key331, 2), (key263, 2), (key321, 2), (key253, 2), (key435, 2), (key316, 2), (key248, 2), (key662, 2), (key661, 2), (key658, 2), (key656, 2), (key657, 2), (key655, 2), (key489, 2), (key488, 2), (key347, 2), (key278, 2), (key346, 2), (key277, 2), (key421, 2), (key400, 2), (key331, 2), (key263, 2), (key307, 2), (key241, 2), (key406, 2), (key385, 2), (key316, 2), (key248, 2), (key302, 2), (key236, 2), (key453, 2), (key421, 2), (key331, 2), (key445, 2), (key400, 2), (key263, 2), (key411, 2), (key321, 2), (key390, 2), (key253, 2), (key307, 2), (key241, 2)]

def rawRow20312 : Integer.Sparse Key := [(key655, 2), (key655, 2), (key656, 2), (key657, 2), (key657, 2), (key660, 2), (key660, 2), (key661, 2), (key661, 2), (key658, 2), (key662, 2), (key662, 2), (key277, 2), (key277, 2), (key278, 2), (key346, 2), (key346, 2), (key487, 2), (key487, 2), (key488, 2), (key488, 2), (key347, 2), (key489, 2), (key489, 2), (key241, 2), (key241, 2), (key253, 2), (key253, 2), (key263, 2), (key263, 2), (key307, 2), (key307, 2), (key390, 2), (key390, 2), (key400, 2), (key400, 2), (key321, 2), (key321, 2), (key411, 2), (key411, 2), (key445, 2), (key445, 2), (key331, 2), (key331, 2), (key421, 2), (key421, 2), (key453, 2), (key453, 2), (key236, 2), (key248, 2), (key248, 2), (key302, 2), (key316, 2), (key316, 2), (key385, 2), (key385, 2), (key406, 2), (key406, 2), (key435, 2), (key435, 2)]

def rawRow20313 : Integer.Sparse Key := [(key655, 2), (key656, 2), (key655, 2), (key660, 2), (key661, 2), (key657, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key658, 2), (key662, 2), (key277, 2), (key278, 2), (key277, 2), (key487, 2), (key488, 2), (key346, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key347, 2), (key489, 2), (key253, 2), (key263, 2), (key241, 2), (key263, 2), (key241, 2), (key253, 2), (key390, 2), (key400, 2), (key307, 2), (key400, 2), (key307, 2), (key390, 2), (key411, 2), (key445, 2), (key321, 2), (key445, 2), (key321, 2), (key411, 2), (key421, 2), (key453, 2), (key331, 2), (key453, 2), (key331, 2), (key421, 2), (key248, 2), (key236, 2), (key248, 2), (key316, 2), (key302, 2), (key316, 2), (key406, 2), (key435, 2), (key385, 2), (key435, 2), (key385, 2), (key406, 2)]

def rawRow20314 : Integer.Sparse Key := [(key656, 2), (key655, 2), (key655, 2), (key661, 2), (key660, 2), (key661, 2), (key657, 2), (key660, 2), (key657, 2), (key662, 2), (key662, 2), (key658, 2), (key278, 2), (key277, 2), (key277, 2), (key488, 2), (key487, 2), (key488, 2), (key346, 2), (key487, 2), (key346, 2), (key489, 2), (key489, 2), (key347, 2), (key263, 2), (key253, 2), (key263, 2), (key241, 2), (key253, 2), (key241, 2), (key400, 2), (key390, 2), (key400, 2), (key307, 2), (key390, 2), (key307, 2), (key445, 2), (key411, 2), (key445, 2), (key321, 2), (key411, 2), (key321, 2), (key453, 2), (key421, 2), (key453, 2), (key331, 2), (key421, 2), (key331, 2), (key248, 2), (key248, 2), (key236, 2), (key316, 2), (key316, 2), (key302, 2), (key435, 2), (key406, 2), (key435, 2), (key385, 2), (key406, 2), (key385, 2)]

def rawRow20315 : Integer.Sparse Key := [(key657, 2), (key657, 2), (key658, 2), (key655, 2), (key655, 2), (key660, 2), (key660, 2), (key662, 2), (key662, 2), (key656, 2), (key661, 2), (key661, 2), (key346, 2), (key346, 2), (key347, 2), (key277, 2), (key277, 2), (key487, 2), (key487, 2), (key489, 2), (key489, 2), (key278, 2), (key488, 2), (key488, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key331, 2), (key331, 2), (key241, 2), (key241, 2), (key411, 2), (key411, 2), (key421, 2), (key421, 2), (key253, 2), (key253, 2), (key390, 2), (key390, 2), (key453, 2), (key453, 2), (key263, 2), (key263, 2), (key400, 2), (key400, 2), (key445, 2), (key445, 2), (key302, 2), (key316, 2), (key316, 2), (key236, 2), (key406, 2), (key406, 2), (key248, 2), (key248, 2), (key316, 2), (key316, 2), (key435, 2), (key435, 2)]

def rawRow20316 : Integer.Sparse Key := [(key657, 2), (key658, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key662, 2), (key655, 2), (key660, 2), (key661, 2), (key656, 2), (key661, 2), (key346, 2), (key347, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key489, 2), (key277, 2), (key487, 2), (key488, 2), (key278, 2), (key488, 2), (key321, 2), (key331, 2), (key307, 2), (key331, 2), (key307, 2), (key321, 2), (key411, 2), (key421, 2), (key241, 2), (key421, 2), (key241, 2), (key411, 2), (key390, 2), (key453, 2), (key253, 2), (key453, 2), (key253, 2), (key390, 2), (key400, 2), (key445, 2), (key263, 2), (key445, 2), (key263, 2), (key400, 2), (key316, 2), (key302, 2), (key316, 2), (key406, 2), (key236, 2), (key406, 2), (key316, 2), (key435, 2), (key248, 2), (key435, 2), (key248, 2), (key316, 2)]

def rawRow20317 : Integer.Sparse Key := [(key658, 2), (key657, 2), (key657, 2), (key662, 2), (key660, 2), (key662, 2), (key655, 2), (key660, 2), (key655, 2), (key661, 2), (key661, 2), (key656, 2), (key347, 2), (key346, 2), (key346, 2), (key489, 2), (key487, 2), (key489, 2), (key277, 2), (key487, 2), (key277, 2), (key488, 2), (key488, 2), (key278, 2), (key331, 2), (key321, 2), (key331, 2), (key307, 2), (key321, 2), (key307, 2), (key421, 2), (key411, 2), (key421, 2), (key241, 2), (key411, 2), (key241, 2), (key453, 2), (key390, 2), (key453, 2), (key253, 2), (key390, 2), (key253, 2), (key445, 2), (key400, 2), (key445, 2), (key263, 2), (key400, 2), (key263, 2), (key316, 2), (key316, 2), (key302, 2), (key406, 2), (key406, 2), (key236, 2), (key435, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key248, 2)]

def rawRow20318 : Integer.Sparse Key := [(key660, 2), (key661, 2), (key662, 2), (key655, 2), (key656, 2), (key657, 2), (key661, 2), (key658, 2), (key662, 2), (key655, 2), (key657, 2), (key660, 2), (key487, 2), (key488, 2), (key489, 2), (key277, 2), (key278, 2), (key346, 2), (key488, 2), (key347, 2), (key489, 2), (key277, 2), (key346, 2), (key487, 2), (key390, 2), (key400, 2), (key411, 2), (key445, 2), (key421, 2), (key453, 2), (key253, 2), (key263, 2), (key321, 2), (key445, 2), (key331, 2), (key453, 2), (key241, 2), (key263, 2), (key307, 2), (key400, 2), (key331, 2), (key421, 2), (key241, 2), (key253, 2), (key307, 2), (key390, 2), (key321, 2), (key411, 2), (key385, 2), (key406, 2), (key435, 2), (key248, 2), (key316, 2), (key435, 2), (key236, 2), (key248, 2), (key302, 2), (key316, 2), (key385, 2), (key406, 2)]

def rawRow20319 : Integer.Sparse Key := [(key661, 2), (key660, 2), (key662, 2), (key656, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key658, 2), (key655, 2), (key660, 2), (key657, 2), (key488, 2), (key487, 2), (key489, 2), (key278, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key347, 2), (key277, 2), (key487, 2), (key346, 2), (key400, 2), (key390, 2), (key445, 2), (key411, 2), (key453, 2), (key421, 2), (key263, 2), (key253, 2), (key445, 2), (key321, 2), (key453, 2), (key331, 2), (key263, 2), (key241, 2), (key400, 2), (key307, 2), (key421, 2), (key331, 2), (key253, 2), (key241, 2), (key390, 2), (key307, 2), (key411, 2), (key321, 2), (key385, 2), (key435, 2), (key406, 2), (key248, 2), (key435, 2), (key316, 2), (key248, 2), (key236, 2), (key316, 2), (key302, 2), (key406, 2), (key385, 2)]

def rawRow20320 : Integer.Sparse Key := [(key660, 2), (key662, 2), (key661, 2), (key657, 2), (key658, 2), (key655, 2), (key662, 2), (key656, 2), (key661, 2), (key657, 2), (key655, 2), (key660, 2), (key487, 2), (key489, 2), (key488, 2), (key346, 2), (key347, 2), (key277, 2), (key489, 2), (key278, 2), (key488, 2), (key346, 2), (key277, 2), (key487, 2), (key411, 2), (key421, 2), (key390, 2), (key453, 2), (key400, 2), (key445, 2), (key321, 2), (key331, 2), (key253, 2), (key453, 2), (key263, 2), (key445, 2), (key307, 2), (key331, 2), (key241, 2), (key421, 2), (key263, 2), (key400, 2), (key307, 2), (key321, 2), (key241, 2), (key411, 2), (key253, 2), (key390, 2), (key406, 2), (key385, 2), (key435, 2), (key316, 2), (key248, 2), (key435, 2), (key302, 2), (key316, 2), (key236, 2), (key406, 2), (key248, 2), (key316, 2)]

def rawRow20321 : Integer.Sparse Key := [(key662, 2), (key660, 2), (key661, 2), (key658, 2), (key657, 2), (key662, 2), (key655, 2), (key661, 2), (key656, 2), (key657, 2), (key660, 2), (key655, 2), (key489, 2), (key487, 2), (key488, 2), (key347, 2), (key346, 2), (key489, 2), (key277, 2), (key488, 2), (key278, 2), (key346, 2), (key487, 2), (key277, 2), (key421, 2), (key411, 2), (key453, 2), (key390, 2), (key445, 2), (key400, 2), (key331, 2), (key321, 2), (key453, 2), (key253, 2), (key445, 2), (key263, 2), (key331, 2), (key307, 2), (key421, 2), (key241, 2), (key400, 2), (key263, 2), (key321, 2), (key307, 2), (key411, 2), (key241, 2), (key390, 2), (key253, 2), (key406, 2), (key435, 2), (key385, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key302, 2), (key406, 2), (key236, 2), (key316, 2), (key248, 2)]

def rawRow20322 : Integer.Sparse Key := [(key661, 2), (key662, 2), (key660, 2), (key661, 2), (key662, 2), (key656, 2), (key658, 2), (key655, 2), (key657, 2), (key660, 2), (key655, 2), (key657, 2), (key488, 2), (key489, 2), (key487, 2), (key488, 2), (key489, 2), (key278, 2), (key347, 2), (key277, 2), (key346, 2), (key487, 2), (key277, 2), (key346, 2), (key445, 2), (key453, 2), (key400, 2), (key421, 2), (key390, 2), (key411, 2), (key445, 2), (key453, 2), (key263, 2), (key331, 2), (key253, 2), (key321, 2), (key400, 2), (key421, 2), (key263, 2), (key331, 2), (key241, 2), (key307, 2), (key390, 2), (key411, 2), (key253, 2), (key321, 2), (key241, 2), (key307, 2), (key435, 2), (key385, 2), (key406, 2), (key435, 2), (key248, 2), (key316, 2), (key385, 2), (key406, 2), (key248, 2), (key316, 2), (key236, 2), (key302, 2)]

def rawRow20323 : Integer.Sparse Key := [(key662, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key658, 2), (key656, 2), (key657, 2), (key655, 2), (key660, 2), (key657, 2), (key655, 2), (key489, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key347, 2), (key278, 2), (key346, 2), (key277, 2), (key487, 2), (key346, 2), (key277, 2), (key453, 2), (key445, 2), (key421, 2), (key400, 2), (key411, 2), (key390, 2), (key453, 2), (key445, 2), (key331, 2), (key263, 2), (key321, 2), (key253, 2), (key421, 2), (key400, 2), (key331, 2), (key263, 2), (key307, 2), (key241, 2), (key411, 2), (key390, 2), (key321, 2), (key253, 2), (key307, 2), (key241, 2), (key435, 2), (key406, 2), (key385, 2), (key435, 2), (key316, 2), (key248, 2), (key406, 2), (key385, 2), (key316, 2), (key248, 2), (key302, 2), (key236, 2)]

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

def rawRow2030 : Integer.Sparse Key := [(key971, -2), (key975, -2), (key975, -2), (key975, 6), (key1085, 2), (key1089, 2), (key1089, 2), (key1089, -2), (key1089, -2), (key1179, -2), (key1161, -6), (key1161, 2), (key1161, 2), (key1217, 2)]

def rawRow2031 : Integer.Sparse Key := [(key975, -2), (key971, -2), (key975, -2), (key975, 6), (key1089, 2), (key1085, 2), (key1089, 2), (key1089, -2), (key1179, -2), (key1089, -2), (key1161, -6), (key1161, 2), (key1217, 2), (key1161, 2)]

def rawRow2032 : Integer.Sparse Key := [(key975, -2), (key975, -2), (key971, -2), (key975, 6), (key1089, 2), (key1089, 2), (key1085, 2), (key1179, -2), (key1089, -2), (key1089, -2), (key1161, -6), (key1217, 2), (key1161, 2), (key1161, 2)]

def rawRow2034 : Integer.Sparse Key := [(key1085, -2), (key1089, -2), (key1089, -2), (key1161, 6), (key971, 2), (key975, 2), (key975, 2), (key1161, -2), (key1161, -2), (key1217, -2), (key975, -6), (key1089, 2), (key1089, 2), (key1179, 2)]

def rawRow2035 : Integer.Sparse Key := [(key1089, -2), (key1085, -2), (key1089, -2), (key1161, 6), (key975, 2), (key971, 2), (key975, 2), (key1161, -2), (key1217, -2), (key1161, -2), (key975, -6), (key1089, 2), (key1179, 2), (key1089, 2)]

def rawRow2036 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1085, -2), (key1161, 6), (key975, 2), (key975, 2), (key971, 2), (key1217, -2), (key1161, -2), (key1161, -2), (key975, -6), (key1179, 2), (key1089, 2), (key1089, 2)]

def rawRow2037 : Integer.Sparse Key := [(key1089, -2), (key1089, -2), (key1161, -2), (key1085, 6), (key1179, 2), (key1179, 2), (key1217, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1179, -6), (key975, 2), (key1089, 2), (key1089, 2)]

def rawRow2038 : Integer.Sparse Key := [(key1089, -2), (key1161, -2), (key1089, -2), (key1085, 6), (key1179, 2), (key1217, 2), (key1179, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1179, -6), (key1089, 2), (key975, 2), (key1089, 2)]

def rawRow2039 : Integer.Sparse Key := [(key1161, -2), (key1089, -2), (key1089, -2), (key1085, 6), (key1217, 2), (key1179, 2), (key1179, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1179, -6), (key1089, 2), (key1089, 2), (key975, 2)]

def rawRow2041 : Integer.Sparse Key := [(key1179, -2), (key1179, -2), (key1217, -2), (key1179, 6), (key1089, 2), (key1089, 2), (key1161, 2), (key975, -2), (key1089, -2), (key1089, -2), (key1085, -6), (key971, 2), (key1085, 2), (key1085, 2)]

def rawRow2042 : Integer.Sparse Key := [(key1179, -2), (key1217, -2), (key1179, -2), (key1179, 6), (key1089, 2), (key1161, 2), (key1089, 2), (key1089, -2), (key975, -2), (key1089, -2), (key1085, -6), (key1085, 2), (key971, 2), (key1085, 2)]

def rawRow2043 : Integer.Sparse Key := [(key1217, -2), (key1179, -2), (key1179, -2), (key1179, 6), (key1161, 2), (key1089, 2), (key1089, 2), (key1089, -2), (key1089, -2), (key975, -2), (key1085, -6), (key1085, 2), (key1085, 2), (key971, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow253 : Integer.Sparse Key := [(key242, -1), (key244, -1), (key242, 2), (key264, 1), (key265, 1), (key254, -1), (key264, -1), (key274, -2), (key269, 1), (key274, 1), (key308, 1), (key310, 1), (key308, -2), (key332, -1), (key333, -1), (key322, 1), (key332, 1), (key343, 2), (key337, -1), (key343, -1), (key401, -1), (key402, -1), (key391, 1), (key401, 1), (key422, 1), (key423, 1), (key412, -1), (key422, -1), (key478, -1), (key484, -1), (key472, 1), (key484, 1), (key575, 2), (key570, -1), (key575, -1), (key586, -2), (key580, 1), (key586, 1), (key604, 1), (key610, 1), (key598, -1), (key610, -1)]

def rawRow254 : Integer.Sparse Key := [(key244, -1), (key242, -1), (key242, 2), (key265, 1), (key264, 1), (key264, -1), (key254, -1), (key274, -2), (key274, 1), (key269, 1), (key310, 1), (key308, 1), (key308, -2), (key333, -1), (key332, -1), (key332, 1), (key322, 1), (key343, 2), (key343, -1), (key337, -1), (key402, -1), (key401, -1), (key401, 1), (key391, 1), (key423, 1), (key422, 1), (key422, -1), (key412, -1), (key484, -1), (key478, -1), (key484, 1), (key472, 1), (key575, 2), (key575, -1), (key570, -1), (key586, -2), (key586, 1), (key580, 1), (key610, 1), (key604, 1), (key610, -1), (key598, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2058 : Integer.Sparse Key := [(key2354, -2), (key2358, -2), (key2358, -2), (key2358, 6), (key2449, 2), (key2453, 2), (key2453, 2), (key2453, -2), (key2453, -2), (key2529, -2), (key2514, -6), (key2514, 2), (key2514, 2), (key2559, 2)]

def rawRow2059 : Integer.Sparse Key := [(key2358, -2), (key2354, -2), (key2358, -2), (key2358, 6), (key2453, 2), (key2449, 2), (key2453, 2), (key2453, -2), (key2529, -2), (key2453, -2), (key2514, -6), (key2514, 2), (key2559, 2), (key2514, 2)]

def rawRow2060 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2354, -2), (key2358, 6), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, -2), (key2453, -2), (key2453, -2), (key2514, -6), (key2559, 2), (key2514, 2), (key2514, 2)]

def rawRow2062 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2354, 2), (key2358, 2), (key2358, 2), (key2514, -2), (key2514, -2), (key2559, -2), (key2358, -6), (key2453, 2), (key2453, 2), (key2529, 2)]

def rawRow2063 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2453, -2), (key2514, 6), (key2358, 2), (key2354, 2), (key2358, 2), (key2514, -2), (key2559, -2), (key2514, -2), (key2358, -6), (key2453, 2), (key2529, 2), (key2453, 2)]

def rawRow2064 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2449, -2), (key2514, 6), (key2358, 2), (key2358, 2), (key2354, 2), (key2559, -2), (key2514, -2), (key2514, -2), (key2358, -6), (key2529, 2), (key2453, 2), (key2453, 2)]

def rawRow2065 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2514, -2), (key2449, 6), (key2529, 2), (key2529, 2), (key2559, 2), (key2354, -2), (key2449, -2), (key2449, -2), (key2529, -6), (key2358, 2), (key2453, 2), (key2453, 2)]

def rawRow2066 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2453, -2), (key2449, 6), (key2529, 2), (key2559, 2), (key2529, 2), (key2449, -2), (key2354, -2), (key2449, -2), (key2529, -6), (key2453, 2), (key2358, 2), (key2453, 2)]

def rawRow2067 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2559, 2), (key2529, 2), (key2529, 2), (key2449, -2), (key2449, -2), (key2354, -2), (key2529, -6), (key2453, 2), (key2453, 2), (key2358, 2)]

def rawRow2069 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2559, -2), (key2529, 6), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, -2), (key2453, -2), (key2453, -2), (key2449, -6), (key2354, 2), (key2449, 2), (key2449, 2)]

def rawRow2070 : Integer.Sparse Key := [(key2529, -2), (key2559, -2), (key2529, -2), (key2529, 6), (key2453, 2), (key2514, 2), (key2453, 2), (key2453, -2), (key2358, -2), (key2453, -2), (key2449, -6), (key2449, 2), (key2354, 2), (key2449, 2)]

def rawRow2071 : Integer.Sparse Key := [(key2559, -2), (key2529, -2), (key2529, -2), (key2529, 6), (key2514, 2), (key2453, 2), (key2453, 2), (key2453, -2), (key2453, -2), (key2358, -2), (key2449, -6), (key2449, 2), (key2449, 2), (key2354, 2)]

def rawRow2072 : Integer.Sparse Key := [(key2353, -2), (key2356, -2), (key2356, -2), (key2356, 6), (key2448, 2), (key2451, 2), (key2451, 2), (key2451, -2), (key2451, -2), (key2513, -2), (key2527, -6), (key2527, 2), (key2527, 2), (key2558, 2)]

def rawRow2073 : Integer.Sparse Key := [(key2356, -2), (key2353, -2), (key2356, -2), (key2356, 6), (key2451, 2), (key2448, 2), (key2451, 2), (key2451, -2), (key2513, -2), (key2451, -2), (key2527, -6), (key2527, 2), (key2558, 2), (key2527, 2)]

def rawRow2074 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2353, -2), (key2356, 6), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, -2), (key2451, -2), (key2451, -2), (key2527, -6), (key2558, 2), (key2527, 2), (key2527, 2)]

def rawRow2076 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2451, -2), (key2513, 6), (key2353, 2), (key2356, 2), (key2356, 2), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, -6), (key2451, 2), (key2451, 2), (key2513, 2)]

def rawRow2077 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2451, -2), (key2513, 6), (key2356, 2), (key2353, 2), (key2356, 2), (key2527, -2), (key2558, -2), (key2527, -2), (key2356, -6), (key2451, 2), (key2513, 2), (key2451, 2)]

def rawRow2078 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2448, -2), (key2513, 6), (key2356, 2), (key2356, 2), (key2353, 2), (key2558, -2), (key2527, -2), (key2527, -2), (key2356, -6), (key2513, 2), (key2451, 2), (key2451, 2)]

def rawRow2079 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2513, -2), (key2448, 6), (key2527, 2), (key2527, 2), (key2558, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2513, -6), (key2356, 2), (key2451, 2), (key2451, 2)]

def rawRow2080 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2451, -2), (key2448, 6), (key2527, 2), (key2558, 2), (key2527, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2513, -6), (key2451, 2), (key2356, 2), (key2451, 2)]

def rawRow2081 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2558, 2), (key2527, 2), (key2527, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2513, -6), (key2451, 2), (key2451, 2), (key2356, 2)]

def rawRow2083 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2558, -2), (key2527, 6), (key2451, 2), (key2451, 2), (key2513, 2), (key2356, -2), (key2451, -2), (key2451, -2), (key2448, -6), (key2353, 2), (key2448, 2), (key2448, 2)]

def rawRow2084 : Integer.Sparse Key := [(key2527, -2), (key2558, -2), (key2527, -2), (key2527, 6), (key2451, 2), (key2513, 2), (key2451, 2), (key2451, -2), (key2356, -2), (key2451, -2), (key2448, -6), (key2448, 2), (key2353, 2), (key2448, 2)]

def rawRow2085 : Integer.Sparse Key := [(key2558, -2), (key2527, -2), (key2527, -2), (key2527, 6), (key2513, 2), (key2451, 2), (key2451, 2), (key2451, -2), (key2451, -2), (key2356, -2), (key2448, -6), (key2448, 2), (key2448, 2), (key2353, 2)]

def rawRow2119 : Integer.Sparse Key := [(key1308, -6), (key1288, 2), (key1308, 2), (key1334, 2), (key1538, 6), (key1383, -2), (key1538, -2), (key1769, -2), (key1565, -2), (key1614, -2), (key1652, -2), (key1416, 2), (key1614, 2), (key1810, 2)]

def rawRow2120 : Integer.Sparse Key := [(key1308, -6), (key1288, 2), (key1334, 2), (key1308, 2), (key1538, 6), (key1383, -2), (key1769, -2), (key1538, -2), (key1565, -2), (key1652, -2), (key1614, -2), (key1416, 2), (key1810, 2), (key1614, 2)]

def rawRow2121 : Integer.Sparse Key := [(key1308, -6), (key1308, 2), (key1288, 2), (key1334, 2), (key1538, 6), (key1538, -2), (key1383, -2), (key1769, -2), (key1614, -2), (key1565, -2), (key1652, -2), (key1614, 2), (key1416, 2), (key1810, 2)]

def rawRow2122 : Integer.Sparse Key := [(key1308, -6), (key1308, 2), (key1334, 2), (key1288, 2), (key1538, 6), (key1538, -2), (key1769, -2), (key1383, -2), (key1614, -2), (key1652, -2), (key1565, -2), (key1614, 2), (key1810, 2), (key1416, 2)]

def rawRow2123 : Integer.Sparse Key := [(key1308, -6), (key1334, 2), (key1288, 2), (key1308, 2), (key1538, 6), (key1769, -2), (key1383, -2), (key1538, -2), (key1652, -2), (key1565, -2), (key1614, -2), (key1810, 2), (key1416, 2), (key1614, 2)]

def rawRow2124 : Integer.Sparse Key := [(key1308, -6), (key1334, 2), (key1308, 2), (key1288, 2), (key1538, 6), (key1769, -2), (key1538, -2), (key1383, -2), (key1652, -2), (key1614, -2), (key1565, -2), (key1810, 2), (key1614, 2), (key1416, 2)]

def rawRow2128 : Integer.Sparse Key := [(key1416, -6), (key1383, 2), (key1416, 2), (key1452, 2), (key1565, 6), (key1288, -2), (key1565, -2), (key1785, -2), (key1538, -2), (key1614, -2), (key1652, -2), (key1308, 2), (key1614, 2), (key1810, 2)]

def rawRow2129 : Integer.Sparse Key := [(key1416, -6), (key1383, 2), (key1452, 2), (key1416, 2), (key1565, 6), (key1288, -2), (key1785, -2), (key1565, -2), (key1538, -2), (key1652, -2), (key1614, -2), (key1308, 2), (key1810, 2), (key1614, 2)]

def rawRow2130 : Integer.Sparse Key := [(key1416, -6), (key1416, 2), (key1383, 2), (key1452, 2), (key1565, 6), (key1565, -2), (key1288, -2), (key1785, -2), (key1614, -2), (key1538, -2), (key1652, -2), (key1614, 2), (key1308, 2), (key1810, 2)]

def rawRow2131 : Integer.Sparse Key := [(key1416, -6), (key1416, 2), (key1452, 2), (key1383, 2), (key1565, 6), (key1565, -2), (key1785, -2), (key1288, -2), (key1614, -2), (key1652, -2), (key1538, -2), (key1614, 2), (key1810, 2), (key1308, 2)]

def rawRow2132 : Integer.Sparse Key := [(key1416, -6), (key1452, 2), (key1383, 2), (key1416, 2), (key1565, 6), (key1785, -2), (key1288, -2), (key1565, -2), (key1652, -2), (key1538, -2), (key1614, -2), (key1810, 2), (key1308, 2), (key1614, 2)]

def rawRow2133 : Integer.Sparse Key := [(key1416, -6), (key1452, 2), (key1416, 2), (key1383, 2), (key1565, 6), (key1785, -2), (key1565, -2), (key1288, -2), (key1652, -2), (key1614, -2), (key1538, -2), (key1810, 2), (key1614, 2), (key1308, 2)]

def rawRow2134 : Integer.Sparse Key := [(key1538, -6), (key1565, 2), (key1614, 2), (key1652, 2), (key1308, 6), (key1416, -2), (key1614, -2), (key1810, -2), (key1288, -2), (key1308, -2), (key1334, -2), (key1383, 2), (key1538, 2), (key1769, 2)]

def rawRow2135 : Integer.Sparse Key := [(key1538, -6), (key1565, 2), (key1652, 2), (key1614, 2), (key1308, 6), (key1416, -2), (key1810, -2), (key1614, -2), (key1288, -2), (key1334, -2), (key1308, -2), (key1383, 2), (key1769, 2), (key1538, 2)]

def rawRow2136 : Integer.Sparse Key := [(key1538, -6), (key1614, 2), (key1565, 2), (key1652, 2), (key1308, 6), (key1614, -2), (key1416, -2), (key1810, -2), (key1308, -2), (key1288, -2), (key1334, -2), (key1538, 2), (key1383, 2), (key1769, 2)]

def rawRow2137 : Integer.Sparse Key := [(key1538, -6), (key1614, 2), (key1652, 2), (key1565, 2), (key1308, 6), (key1614, -2), (key1810, -2), (key1416, -2), (key1308, -2), (key1334, -2), (key1288, -2), (key1538, 2), (key1769, 2), (key1383, 2)]

def rawRow2138 : Integer.Sparse Key := [(key1538, -6), (key1652, 2), (key1565, 2), (key1614, 2), (key1308, 6), (key1810, -2), (key1416, -2), (key1614, -2), (key1334, -2), (key1288, -2), (key1308, -2), (key1769, 2), (key1383, 2), (key1538, 2)]

def rawRow2139 : Integer.Sparse Key := [(key1538, -6), (key1652, 2), (key1614, 2), (key1565, 2), (key1308, 6), (key1810, -2), (key1614, -2), (key1416, -2), (key1334, -2), (key1308, -2), (key1288, -2), (key1769, 2), (key1538, 2), (key1383, 2)]

def rawRow2140 : Integer.Sparse Key := [(key1565, -6), (key1538, 2), (key1614, 2), (key1652, 2), (key1416, 6), (key1308, -2), (key1614, -2), (key1810, -2), (key1383, -2), (key1416, -2), (key1452, -2), (key1288, 2), (key1565, 2), (key1785, 2)]

def rawRow2141 : Integer.Sparse Key := [(key1565, -6), (key1538, 2), (key1652, 2), (key1614, 2), (key1416, 6), (key1308, -2), (key1810, -2), (key1614, -2), (key1383, -2), (key1452, -2), (key1416, -2), (key1288, 2), (key1785, 2), (key1565, 2)]

def rawRow2142 : Integer.Sparse Key := [(key1565, -6), (key1614, 2), (key1538, 2), (key1652, 2), (key1416, 6), (key1614, -2), (key1308, -2), (key1810, -2), (key1416, -2), (key1383, -2), (key1452, -2), (key1565, 2), (key1288, 2), (key1785, 2)]

def rawRow2143 : Integer.Sparse Key := [(key1565, -6), (key1614, 2), (key1652, 2), (key1538, 2), (key1416, 6), (key1614, -2), (key1810, -2), (key1308, -2), (key1416, -2), (key1452, -2), (key1383, -2), (key1565, 2), (key1785, 2), (key1288, 2)]

def rawRow2144 : Integer.Sparse Key := [(key1565, -6), (key1652, 2), (key1538, 2), (key1614, 2), (key1416, 6), (key1810, -2), (key1308, -2), (key1614, -2), (key1452, -2), (key1383, -2), (key1416, -2), (key1785, 2), (key1288, 2), (key1565, 2)]

def rawRow2145 : Integer.Sparse Key := [(key1565, -6), (key1652, 2), (key1614, 2), (key1538, 2), (key1416, 6), (key1810, -2), (key1614, -2), (key1308, -2), (key1452, -2), (key1416, -2), (key1383, -2), (key1785, 2), (key1565, 2), (key1288, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2179 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key1013, -2), (key999, 6), (key1107, 2), (key1112, 2), (key1121, 2), (key1034, -2), (key1112, -2), (key1191, -2), (key1148, -6), (key1069, 2), (key1148, 2), (key1210, 2)]

def rawRow2180 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key1013, -2), (key999, 6), (key1112, 2), (key1107, 2), (key1121, 2), (key1034, -2), (key1191, -2), (key1112, -2), (key1148, -6), (key1069, 2), (key1210, 2), (key1148, 2)]

def rawRow2181 : Integer.Sparse Key := [(key994, -2), (key1013, -2), (key999, -2), (key999, 6), (key1107, 2), (key1121, 2), (key1112, 2), (key1112, -2), (key1034, -2), (key1191, -2), (key1148, -6), (key1148, 2), (key1069, 2), (key1210, 2)]

def rawRow2182 : Integer.Sparse Key := [(key1013, -2), (key994, -2), (key999, -2), (key999, 6), (key1121, 2), (key1107, 2), (key1112, 2), (key1112, -2), (key1191, -2), (key1034, -2), (key1148, -6), (key1148, 2), (key1210, 2), (key1069, 2)]

def rawRow2183 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key994, -2), (key999, 6), (key1112, 2), (key1121, 2), (key1107, 2), (key1191, -2), (key1034, -2), (key1112, -2), (key1148, -6), (key1210, 2), (key1069, 2), (key1148, 2)]

def rawRow2184 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key994, -2), (key999, 6), (key1121, 2), (key1112, 2), (key1107, 2), (key1191, -2), (key1112, -2), (key1034, -2), (key1148, -6), (key1210, 2), (key1148, 2), (key1069, 2)]

def rawRow2188 : Integer.Sparse Key := [(key1029, -2), (key1034, -2), (key1069, -2), (key1034, 6), (key1107, 2), (key1112, 2), (key1148, 2), (key999, -2), (key1112, -2), (key1191, -2), (key1121, -6), (key1013, 2), (key1121, 2), (key1197, 2)]

def rawRow2189 : Integer.Sparse Key := [(key1034, -2), (key1029, -2), (key1069, -2), (key1034, 6), (key1112, 2), (key1107, 2), (key1148, 2), (key999, -2), (key1191, -2), (key1112, -2), (key1121, -6), (key1013, 2), (key1197, 2), (key1121, 2)]

def rawRow2190 : Integer.Sparse Key := [(key1029, -2), (key1069, -2), (key1034, -2), (key1034, 6), (key1107, 2), (key1148, 2), (key1112, 2), (key1112, -2), (key999, -2), (key1191, -2), (key1121, -6), (key1121, 2), (key1013, 2), (key1197, 2)]

def rawRow2191 : Integer.Sparse Key := [(key1069, -2), (key1029, -2), (key1034, -2), (key1034, 6), (key1148, 2), (key1107, 2), (key1112, 2), (key1112, -2), (key1191, -2), (key999, -2), (key1121, -6), (key1121, 2), (key1197, 2), (key1013, 2)]

def rawRow2192 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1029, -2), (key1034, 6), (key1112, 2), (key1148, 2), (key1107, 2), (key1191, -2), (key999, -2), (key1112, -2), (key1121, -6), (key1197, 2), (key1013, 2), (key1121, 2)]

def rawRow2193 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1029, -2), (key1034, 6), (key1148, 2), (key1112, 2), (key1107, 2), (key1191, -2), (key1112, -2), (key999, -2), (key1121, -6), (key1197, 2), (key1121, 2), (key1013, 2)]

def rawRow2194 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1121, -2), (key1148, 6), (key994, 2), (key999, 2), (key1013, 2), (key1069, -2), (key1148, -2), (key1210, -2), (key999, -6), (key1034, 2), (key1112, 2), (key1191, 2)]

def rawRow2195 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1121, -2), (key1148, 6), (key999, 2), (key994, 2), (key1013, 2), (key1069, -2), (key1210, -2), (key1148, -2), (key999, -6), (key1034, 2), (key1191, 2), (key1112, 2)]

def rawRow2196 : Integer.Sparse Key := [(key1107, -2), (key1121, -2), (key1112, -2), (key1148, 6), (key994, 2), (key1013, 2), (key999, 2), (key1148, -2), (key1069, -2), (key1210, -2), (key999, -6), (key1112, 2), (key1034, 2), (key1191, 2)]

def rawRow2197 : Integer.Sparse Key := [(key1121, -2), (key1107, -2), (key1112, -2), (key1148, 6), (key1013, 2), (key994, 2), (key999, 2), (key1148, -2), (key1210, -2), (key1069, -2), (key999, -6), (key1112, 2), (key1191, 2), (key1034, 2)]

def rawRow2198 : Integer.Sparse Key := [(key1112, -2), (key1121, -2), (key1107, -2), (key1148, 6), (key999, 2), (key1013, 2), (key994, 2), (key1210, -2), (key1069, -2), (key1148, -2), (key999, -6), (key1191, 2), (key1034, 2), (key1112, 2)]

def rawRow2199 : Integer.Sparse Key := [(key1121, -2), (key1112, -2), (key1107, -2), (key1148, 6), (key1013, 2), (key999, 2), (key994, 2), (key1210, -2), (key1148, -2), (key1069, -2), (key999, -6), (key1191, 2), (key1112, 2), (key1034, 2)]

def rawRow2200 : Integer.Sparse Key := [(key1107, -2), (key1112, -2), (key1148, -2), (key1121, 6), (key1029, 2), (key1034, 2), (key1069, 2), (key1013, -2), (key1121, -2), (key1197, -2), (key1034, -6), (key999, 2), (key1112, 2), (key1191, 2)]

def rawRow2201 : Integer.Sparse Key := [(key1112, -2), (key1107, -2), (key1148, -2), (key1121, 6), (key1034, 2), (key1029, 2), (key1069, 2), (key1013, -2), (key1197, -2), (key1121, -2), (key1034, -6), (key999, 2), (key1191, 2), (key1112, 2)]

def rawRow2202 : Integer.Sparse Key := [(key1107, -2), (key1148, -2), (key1112, -2), (key1121, 6), (key1029, 2), (key1069, 2), (key1034, 2), (key1121, -2), (key1013, -2), (key1197, -2), (key1034, -6), (key1112, 2), (key999, 2), (key1191, 2)]

def rawRow2203 : Integer.Sparse Key := [(key1148, -2), (key1107, -2), (key1112, -2), (key1121, 6), (key1069, 2), (key1029, 2), (key1034, 2), (key1121, -2), (key1197, -2), (key1013, -2), (key1034, -6), (key1112, 2), (key1191, 2), (key999, 2)]

def rawRow2204 : Integer.Sparse Key := [(key1112, -2), (key1148, -2), (key1107, -2), (key1121, 6), (key1034, 2), (key1069, 2), (key1029, 2), (key1197, -2), (key1013, -2), (key1121, -2), (key1034, -6), (key1191, 2), (key999, 2), (key1112, 2)]

def rawRow2205 : Integer.Sparse Key := [(key1148, -2), (key1112, -2), (key1107, -2), (key1121, 6), (key1069, 2), (key1034, 2), (key1029, 2), (key1197, -2), (key1121, -2), (key1013, -2), (key1034, -6), (key1191, 2), (key1112, 2), (key999, 2)]

def rawRow2209 : Integer.Sparse Key := [(key2623, -6), (key2607, 2), (key2623, 2), (key2634, 2), (key2697, 6), (key2662, -2), (key2697, -2), (key2720, -2), (key2800, -2), (key2850, -2), (key2854, -2), (key2777, 2), (key2850, 2), (key2864, 2)]

def rawRow2210 : Integer.Sparse Key := [(key2623, -6), (key2607, 2), (key2634, 2), (key2623, 2), (key2697, 6), (key2662, -2), (key2720, -2), (key2697, -2), (key2800, -2), (key2854, -2), (key2850, -2), (key2777, 2), (key2864, 2), (key2850, 2)]

def rawRow2211 : Integer.Sparse Key := [(key2623, -6), (key2623, 2), (key2607, 2), (key2634, 2), (key2697, 6), (key2697, -2), (key2662, -2), (key2720, -2), (key2850, -2), (key2800, -2), (key2854, -2), (key2850, 2), (key2777, 2), (key2864, 2)]

def rawRow2212 : Integer.Sparse Key := [(key2623, -6), (key2623, 2), (key2634, 2), (key2607, 2), (key2697, 6), (key2697, -2), (key2720, -2), (key2662, -2), (key2850, -2), (key2854, -2), (key2800, -2), (key2850, 2), (key2864, 2), (key2777, 2)]

def rawRow2213 : Integer.Sparse Key := [(key2623, -6), (key2634, 2), (key2607, 2), (key2623, 2), (key2697, 6), (key2720, -2), (key2662, -2), (key2697, -2), (key2854, -2), (key2800, -2), (key2850, -2), (key2864, 2), (key2777, 2), (key2850, 2)]

def rawRow2214 : Integer.Sparse Key := [(key2623, -6), (key2634, 2), (key2623, 2), (key2607, 2), (key2697, 6), (key2720, -2), (key2697, -2), (key2662, -2), (key2854, -2), (key2850, -2), (key2800, -2), (key2864, 2), (key2850, 2), (key2777, 2)]

def rawRow2218 : Integer.Sparse Key := [(key2777, -6), (key2662, 2), (key2777, 2), (key2788, 2), (key2800, 6), (key2607, -2), (key2800, -2), (key2823, -2), (key2697, -2), (key2850, -2), (key2854, -2), (key2623, 2), (key2850, 2), (key2864, 2)]

def rawRow2219 : Integer.Sparse Key := [(key2777, -6), (key2662, 2), (key2788, 2), (key2777, 2), (key2800, 6), (key2607, -2), (key2823, -2), (key2800, -2), (key2697, -2), (key2854, -2), (key2850, -2), (key2623, 2), (key2864, 2), (key2850, 2)]

def rawRow2220 : Integer.Sparse Key := [(key2777, -6), (key2777, 2), (key2662, 2), (key2788, 2), (key2800, 6), (key2800, -2), (key2607, -2), (key2823, -2), (key2850, -2), (key2697, -2), (key2854, -2), (key2850, 2), (key2623, 2), (key2864, 2)]

def rawRow2221 : Integer.Sparse Key := [(key2777, -6), (key2777, 2), (key2788, 2), (key2662, 2), (key2800, 6), (key2800, -2), (key2823, -2), (key2607, -2), (key2850, -2), (key2854, -2), (key2697, -2), (key2850, 2), (key2864, 2), (key2623, 2)]

def rawRow2222 : Integer.Sparse Key := [(key2777, -6), (key2788, 2), (key2662, 2), (key2777, 2), (key2800, 6), (key2823, -2), (key2607, -2), (key2800, -2), (key2854, -2), (key2697, -2), (key2850, -2), (key2864, 2), (key2623, 2), (key2850, 2)]

def rawRow2223 : Integer.Sparse Key := [(key2777, -6), (key2788, 2), (key2777, 2), (key2662, 2), (key2800, 6), (key2823, -2), (key2800, -2), (key2607, -2), (key2854, -2), (key2850, -2), (key2697, -2), (key2864, 2), (key2850, 2), (key2623, 2)]

def rawRow2224 : Integer.Sparse Key := [(key2697, -6), (key2800, 2), (key2850, 2), (key2854, 2), (key2623, 6), (key2777, -2), (key2850, -2), (key2864, -2), (key2607, -2), (key2623, -2), (key2634, -2), (key2662, 2), (key2697, 2), (key2720, 2)]

def rawRow2225 : Integer.Sparse Key := [(key2697, -6), (key2800, 2), (key2854, 2), (key2850, 2), (key2623, 6), (key2777, -2), (key2864, -2), (key2850, -2), (key2607, -2), (key2634, -2), (key2623, -2), (key2662, 2), (key2720, 2), (key2697, 2)]

def rawRow2226 : Integer.Sparse Key := [(key2697, -6), (key2850, 2), (key2800, 2), (key2854, 2), (key2623, 6), (key2850, -2), (key2777, -2), (key2864, -2), (key2623, -2), (key2607, -2), (key2634, -2), (key2697, 2), (key2662, 2), (key2720, 2)]

def rawRow2227 : Integer.Sparse Key := [(key2697, -6), (key2850, 2), (key2854, 2), (key2800, 2), (key2623, 6), (key2850, -2), (key2864, -2), (key2777, -2), (key2623, -2), (key2634, -2), (key2607, -2), (key2697, 2), (key2720, 2), (key2662, 2)]

def rawRow2228 : Integer.Sparse Key := [(key2697, -6), (key2854, 2), (key2800, 2), (key2850, 2), (key2623, 6), (key2864, -2), (key2777, -2), (key2850, -2), (key2634, -2), (key2607, -2), (key2623, -2), (key2720, 2), (key2662, 2), (key2697, 2)]

def rawRow2229 : Integer.Sparse Key := [(key2697, -6), (key2854, 2), (key2850, 2), (key2800, 2), (key2623, 6), (key2864, -2), (key2850, -2), (key2777, -2), (key2634, -2), (key2623, -2), (key2607, -2), (key2720, 2), (key2697, 2), (key2662, 2)]

def rawRow2230 : Integer.Sparse Key := [(key2800, -6), (key2697, 2), (key2850, 2), (key2854, 2), (key2777, 6), (key2623, -2), (key2850, -2), (key2864, -2), (key2662, -2), (key2777, -2), (key2788, -2), (key2607, 2), (key2800, 2), (key2823, 2)]

def rawRow2231 : Integer.Sparse Key := [(key2800, -6), (key2697, 2), (key2854, 2), (key2850, 2), (key2777, 6), (key2623, -2), (key2864, -2), (key2850, -2), (key2662, -2), (key2788, -2), (key2777, -2), (key2607, 2), (key2823, 2), (key2800, 2)]

def rawRow2232 : Integer.Sparse Key := [(key2800, -6), (key2850, 2), (key2697, 2), (key2854, 2), (key2777, 6), (key2850, -2), (key2623, -2), (key2864, -2), (key2777, -2), (key2662, -2), (key2788, -2), (key2800, 2), (key2607, 2), (key2823, 2)]

def rawRow2233 : Integer.Sparse Key := [(key2800, -6), (key2850, 2), (key2854, 2), (key2697, 2), (key2777, 6), (key2850, -2), (key2864, -2), (key2623, -2), (key2777, -2), (key2788, -2), (key2662, -2), (key2800, 2), (key2823, 2), (key2607, 2)]

def rawRow2234 : Integer.Sparse Key := [(key2800, -6), (key2854, 2), (key2697, 2), (key2850, 2), (key2777, 6), (key2864, -2), (key2623, -2), (key2850, -2), (key2788, -2), (key2662, -2), (key2777, -2), (key2823, 2), (key2607, 2), (key2800, 2)]

def rawRow2235 : Integer.Sparse Key := [(key2800, -6), (key2854, 2), (key2850, 2), (key2697, 2), (key2777, 6), (key2864, -2), (key2850, -2), (key2623, -2), (key2788, -2), (key2777, -2), (key2662, -2), (key2823, 2), (key2800, 2), (key2607, 2)]

def rawRow2269 : Integer.Sparse Key := [(key3048, -2), (key3056, -2), (key3073, -2), (key3052, 2), (key3056, 2), (key3071, 2), (key3097, 2), (key3108, 2), (key3135, 2), (key3108, -6), (key3104, -2), (key3111, -2), (key3137, -2), (key3111, 6)]

def rawRow2270 : Integer.Sparse Key := [(key3056, -2), (key3048, -2), (key3073, -2), (key3056, 2), (key3052, 2), (key3071, 2), (key3108, 2), (key3097, 2), (key3135, 2), (key3108, -6), (key3111, -2), (key3104, -2), (key3137, -2), (key3111, 6)]

def rawRow2271 : Integer.Sparse Key := [(key3048, -2), (key3073, -2), (key3056, -2), (key3052, 2), (key3071, 2), (key3056, 2), (key3097, 2), (key3135, 2), (key3108, 2), (key3108, -6), (key3104, -2), (key3137, -2), (key3111, -2), (key3111, 6)]

def rawRow2272 : Integer.Sparse Key := [(key3073, -2), (key3048, -2), (key3056, -2), (key3071, 2), (key3052, 2), (key3056, 2), (key3135, 2), (key3097, 2), (key3108, 2), (key3108, -6), (key3137, -2), (key3104, -2), (key3111, -2), (key3111, 6)]

def rawRow2273 : Integer.Sparse Key := [(key3056, -2), (key3073, -2), (key3048, -2), (key3056, 2), (key3071, 2), (key3052, 2), (key3108, 2), (key3135, 2), (key3097, 2), (key3108, -6), (key3111, -2), (key3137, -2), (key3104, -2), (key3111, 6)]

def rawRow2274 : Integer.Sparse Key := [(key3073, -2), (key3056, -2), (key3048, -2), (key3071, 2), (key3056, 2), (key3052, 2), (key3135, 2), (key3108, 2), (key3097, 2), (key3108, -6), (key3137, -2), (key3111, -2), (key3104, -2), (key3111, 6)]

def rawRow2278 : Integer.Sparse Key := [(key3048, -2), (key3056, -2), (key3111, -2), (key3052, 2), (key3056, 2), (key3108, 2), (key3062, 2), (key3071, 2), (key3137, 2), (key3071, -6), (key3067, -2), (key3073, -2), (key3135, -2), (key3073, 6)]

def rawRow2279 : Integer.Sparse Key := [(key3056, -2), (key3048, -2), (key3111, -2), (key3056, 2), (key3052, 2), (key3108, 2), (key3071, 2), (key3062, 2), (key3137, 2), (key3071, -6), (key3073, -2), (key3067, -2), (key3135, -2), (key3073, 6)]

def rawRow2280 : Integer.Sparse Key := [(key3048, -2), (key3111, -2), (key3056, -2), (key3052, 2), (key3108, 2), (key3056, 2), (key3062, 2), (key3137, 2), (key3071, 2), (key3071, -6), (key3067, -2), (key3135, -2), (key3073, -2), (key3073, 6)]

def rawRow2281 : Integer.Sparse Key := [(key3111, -2), (key3048, -2), (key3056, -2), (key3108, 2), (key3052, 2), (key3056, 2), (key3137, 2), (key3062, 2), (key3071, 2), (key3071, -6), (key3135, -2), (key3067, -2), (key3073, -2), (key3073, 6)]

def rawRow2282 : Integer.Sparse Key := [(key3056, -2), (key3111, -2), (key3048, -2), (key3056, 2), (key3108, 2), (key3052, 2), (key3071, 2), (key3137, 2), (key3062, 2), (key3071, -6), (key3073, -2), (key3135, -2), (key3067, -2), (key3073, 6)]

def rawRow2283 : Integer.Sparse Key := [(key3111, -2), (key3056, -2), (key3048, -2), (key3108, 2), (key3056, 2), (key3052, 2), (key3137, 2), (key3071, 2), (key3062, 2), (key3071, -6), (key3135, -2), (key3073, -2), (key3067, -2), (key3073, 6)]

def rawRow2284 : Integer.Sparse Key := [(key3097, -2), (key3108, -2), (key3135, -2), (key3104, 2), (key3111, 2), (key3137, 2), (key3048, 2), (key3056, 2), (key3073, 2), (key3111, -6), (key3052, -2), (key3056, -2), (key3071, -2), (key3108, 6)]

def rawRow2285 : Integer.Sparse Key := [(key3108, -2), (key3097, -2), (key3135, -2), (key3111, 2), (key3104, 2), (key3137, 2), (key3056, 2), (key3048, 2), (key3073, 2), (key3111, -6), (key3056, -2), (key3052, -2), (key3071, -2), (key3108, 6)]

def rawRow2286 : Integer.Sparse Key := [(key3097, -2), (key3135, -2), (key3108, -2), (key3104, 2), (key3137, 2), (key3111, 2), (key3048, 2), (key3073, 2), (key3056, 2), (key3111, -6), (key3052, -2), (key3071, -2), (key3056, -2), (key3108, 6)]

def rawRow2287 : Integer.Sparse Key := [(key3135, -2), (key3097, -2), (key3108, -2), (key3137, 2), (key3104, 2), (key3111, 2), (key3073, 2), (key3048, 2), (key3056, 2), (key3111, -6), (key3071, -2), (key3052, -2), (key3056, -2), (key3108, 6)]

def rawRow2288 : Integer.Sparse Key := [(key3108, -2), (key3135, -2), (key3097, -2), (key3111, 2), (key3137, 2), (key3104, 2), (key3056, 2), (key3073, 2), (key3048, 2), (key3111, -6), (key3056, -2), (key3071, -2), (key3052, -2), (key3108, 6)]

def rawRow2289 : Integer.Sparse Key := [(key3135, -2), (key3108, -2), (key3097, -2), (key3137, 2), (key3111, 2), (key3104, 2), (key3073, 2), (key3056, 2), (key3048, 2), (key3111, -6), (key3071, -2), (key3056, -2), (key3052, -2), (key3108, 6)]

def rawRow2290 : Integer.Sparse Key := [(key3062, -2), (key3071, -2), (key3137, -2), (key3067, 2), (key3073, 2), (key3135, 2), (key3048, 2), (key3056, 2), (key3111, 2), (key3073, -6), (key3052, -2), (key3056, -2), (key3108, -2), (key3071, 6)]

def rawRow2291 : Integer.Sparse Key := [(key3071, -2), (key3062, -2), (key3137, -2), (key3073, 2), (key3067, 2), (key3135, 2), (key3056, 2), (key3048, 2), (key3111, 2), (key3073, -6), (key3056, -2), (key3052, -2), (key3108, -2), (key3071, 6)]

def rawRow2292 : Integer.Sparse Key := [(key3062, -2), (key3137, -2), (key3071, -2), (key3067, 2), (key3135, 2), (key3073, 2), (key3048, 2), (key3111, 2), (key3056, 2), (key3073, -6), (key3052, -2), (key3108, -2), (key3056, -2), (key3071, 6)]

def rawRow2293 : Integer.Sparse Key := [(key3137, -2), (key3062, -2), (key3071, -2), (key3135, 2), (key3067, 2), (key3073, 2), (key3111, 2), (key3048, 2), (key3056, 2), (key3073, -6), (key3108, -2), (key3052, -2), (key3056, -2), (key3071, 6)]

def rawRow2294 : Integer.Sparse Key := [(key3071, -2), (key3137, -2), (key3062, -2), (key3073, 2), (key3135, 2), (key3067, 2), (key3056, 2), (key3111, 2), (key3048, 2), (key3073, -6), (key3056, -2), (key3108, -2), (key3052, -2), (key3071, 6)]

def rawRow2295 : Integer.Sparse Key := [(key3137, -2), (key3071, -2), (key3062, -2), (key3135, 2), (key3073, 2), (key3067, 2), (key3111, 2), (key3056, 2), (key3048, 2), (key3073, -6), (key3108, -2), (key3056, -2), (key3052, -2), (key3071, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2329 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key1012, -2), (key997, 6), (key1106, 2), (key1110, 2), (key1120, 2), (key1032, -2), (key1110, -2), (key1189, -2), (key1147, -6), (key1068, 2), (key1147, 2), (key1209, 2)]

def rawRow2330 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key1012, -2), (key997, 6), (key1110, 2), (key1106, 2), (key1120, 2), (key1032, -2), (key1189, -2), (key1110, -2), (key1147, -6), (key1068, 2), (key1209, 2), (key1147, 2)]

def rawRow2331 : Integer.Sparse Key := [(key993, -2), (key1012, -2), (key997, -2), (key997, 6), (key1106, 2), (key1120, 2), (key1110, 2), (key1110, -2), (key1032, -2), (key1189, -2), (key1147, -6), (key1147, 2), (key1068, 2), (key1209, 2)]

def rawRow2332 : Integer.Sparse Key := [(key1012, -2), (key993, -2), (key997, -2), (key997, 6), (key1120, 2), (key1106, 2), (key1110, 2), (key1110, -2), (key1189, -2), (key1032, -2), (key1147, -6), (key1147, 2), (key1209, 2), (key1068, 2)]

def rawRow2333 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key993, -2), (key997, 6), (key1110, 2), (key1120, 2), (key1106, 2), (key1189, -2), (key1032, -2), (key1110, -2), (key1147, -6), (key1209, 2), (key1068, 2), (key1147, 2)]

def rawRow2334 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key993, -2), (key997, 6), (key1120, 2), (key1110, 2), (key1106, 2), (key1189, -2), (key1110, -2), (key1032, -2), (key1147, -6), (key1209, 2), (key1147, 2), (key1068, 2)]

def rawRow2338 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1068, -2), (key1032, 6), (key1106, 2), (key1110, 2), (key1147, 2), (key997, -2), (key1110, -2), (key1189, -2), (key1120, -6), (key1012, 2), (key1120, 2), (key1196, 2)]

def rawRow2339 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1068, -2), (key1032, 6), (key1110, 2), (key1106, 2), (key1147, 2), (key997, -2), (key1189, -2), (key1110, -2), (key1120, -6), (key1012, 2), (key1196, 2), (key1120, 2)]

def rawRow2340 : Integer.Sparse Key := [(key1028, -2), (key1068, -2), (key1032, -2), (key1032, 6), (key1106, 2), (key1147, 2), (key1110, 2), (key1110, -2), (key997, -2), (key1189, -2), (key1120, -6), (key1120, 2), (key1012, 2), (key1196, 2)]

def rawRow2341 : Integer.Sparse Key := [(key1068, -2), (key1028, -2), (key1032, -2), (key1032, 6), (key1147, 2), (key1106, 2), (key1110, 2), (key1110, -2), (key1189, -2), (key997, -2), (key1120, -6), (key1120, 2), (key1196, 2), (key1012, 2)]

def rawRow2342 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1028, -2), (key1032, 6), (key1110, 2), (key1147, 2), (key1106, 2), (key1189, -2), (key997, -2), (key1110, -2), (key1120, -6), (key1196, 2), (key1012, 2), (key1120, 2)]

def rawRow2343 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1028, -2), (key1032, 6), (key1147, 2), (key1110, 2), (key1106, 2), (key1189, -2), (key1110, -2), (key997, -2), (key1120, -6), (key1196, 2), (key1120, 2), (key1012, 2)]

def rawRow2344 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1120, -2), (key1147, 6), (key993, 2), (key997, 2), (key1012, 2), (key1068, -2), (key1147, -2), (key1209, -2), (key997, -6), (key1032, 2), (key1110, 2), (key1189, 2)]

def rawRow2345 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1120, -2), (key1147, 6), (key997, 2), (key993, 2), (key1012, 2), (key1068, -2), (key1209, -2), (key1147, -2), (key997, -6), (key1032, 2), (key1189, 2), (key1110, 2)]

def rawRow2346 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1110, -2), (key1147, 6), (key993, 2), (key1012, 2), (key997, 2), (key1147, -2), (key1068, -2), (key1209, -2), (key997, -6), (key1110, 2), (key1032, 2), (key1189, 2)]

def rawRow2347 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1110, -2), (key1147, 6), (key1012, 2), (key993, 2), (key997, 2), (key1147, -2), (key1209, -2), (key1068, -2), (key997, -6), (key1110, 2), (key1189, 2), (key1032, 2)]

def rawRow2348 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1106, -2), (key1147, 6), (key997, 2), (key1012, 2), (key993, 2), (key1209, -2), (key1068, -2), (key1147, -2), (key997, -6), (key1189, 2), (key1032, 2), (key1110, 2)]

def rawRow2349 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1106, -2), (key1147, 6), (key1012, 2), (key997, 2), (key993, 2), (key1209, -2), (key1147, -2), (key1068, -2), (key997, -6), (key1189, 2), (key1110, 2), (key1032, 2)]

def rawRow2350 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1147, -2), (key1120, 6), (key1028, 2), (key1032, 2), (key1068, 2), (key1012, -2), (key1120, -2), (key1196, -2), (key1032, -6), (key997, 2), (key1110, 2), (key1189, 2)]

def rawRow2351 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1147, -2), (key1120, 6), (key1032, 2), (key1028, 2), (key1068, 2), (key1012, -2), (key1196, -2), (key1120, -2), (key1032, -6), (key997, 2), (key1189, 2), (key1110, 2)]

def rawRow2352 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1110, -2), (key1120, 6), (key1028, 2), (key1068, 2), (key1032, 2), (key1120, -2), (key1012, -2), (key1196, -2), (key1032, -6), (key1110, 2), (key997, 2), (key1189, 2)]

def rawRow2353 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1110, -2), (key1120, 6), (key1068, 2), (key1028, 2), (key1032, 2), (key1120, -2), (key1196, -2), (key1012, -2), (key1032, -6), (key1110, 2), (key1189, 2), (key997, 2)]

def rawRow2354 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1106, -2), (key1120, 6), (key1032, 2), (key1068, 2), (key1028, 2), (key1196, -2), (key1012, -2), (key1120, -2), (key1032, -6), (key1189, 2), (key997, 2), (key1110, 2)]

def rawRow2355 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1106, -2), (key1120, 6), (key1068, 2), (key1032, 2), (key1028, 2), (key1196, -2), (key1120, -2), (key1012, -2), (key1032, -6), (key1189, 2), (key1110, 2), (key997, 2)]

def rawRow2389 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2387, -2), (key2375, 6), (key2465, 2), (key2469, 2), (key2477, 2), (key2403, -2), (key2469, -2), (key2536, -2), (key2500, -6), (key2434, 2), (key2500, 2), (key2552, 2)]

def rawRow2390 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2387, -2), (key2375, 6), (key2469, 2), (key2465, 2), (key2477, 2), (key2403, -2), (key2536, -2), (key2469, -2), (key2500, -6), (key2434, 2), (key2552, 2), (key2500, 2)]

def rawRow2391 : Integer.Sparse Key := [(key2371, -2), (key2387, -2), (key2375, -2), (key2375, 6), (key2465, 2), (key2477, 2), (key2469, 2), (key2469, -2), (key2403, -2), (key2536, -2), (key2500, -6), (key2500, 2), (key2434, 2), (key2552, 2)]

def rawRow2392 : Integer.Sparse Key := [(key2387, -2), (key2371, -2), (key2375, -2), (key2375, 6), (key2477, 2), (key2465, 2), (key2469, 2), (key2469, -2), (key2536, -2), (key2403, -2), (key2500, -6), (key2500, 2), (key2552, 2), (key2434, 2)]

def rawRow2393 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2371, -2), (key2375, 6), (key2469, 2), (key2477, 2), (key2465, 2), (key2536, -2), (key2403, -2), (key2469, -2), (key2500, -6), (key2552, 2), (key2434, 2), (key2500, 2)]

def rawRow2394 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2371, -2), (key2375, 6), (key2477, 2), (key2469, 2), (key2465, 2), (key2536, -2), (key2469, -2), (key2403, -2), (key2500, -6), (key2552, 2), (key2500, 2), (key2434, 2)]

def rawRow2398 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2434, -2), (key2403, 6), (key2465, 2), (key2469, 2), (key2500, 2), (key2375, -2), (key2469, -2), (key2536, -2), (key2477, -6), (key2387, 2), (key2477, 2), (key2541, 2)]

def rawRow2399 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2434, -2), (key2403, 6), (key2469, 2), (key2465, 2), (key2500, 2), (key2375, -2), (key2536, -2), (key2469, -2), (key2477, -6), (key2387, 2), (key2541, 2), (key2477, 2)]

def rawRow2400 : Integer.Sparse Key := [(key2399, -2), (key2434, -2), (key2403, -2), (key2403, 6), (key2465, 2), (key2500, 2), (key2469, 2), (key2469, -2), (key2375, -2), (key2536, -2), (key2477, -6), (key2477, 2), (key2387, 2), (key2541, 2)]

def rawRow2401 : Integer.Sparse Key := [(key2434, -2), (key2399, -2), (key2403, -2), (key2403, 6), (key2500, 2), (key2465, 2), (key2469, 2), (key2469, -2), (key2536, -2), (key2375, -2), (key2477, -6), (key2477, 2), (key2541, 2), (key2387, 2)]

def rawRow2402 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2399, -2), (key2403, 6), (key2469, 2), (key2500, 2), (key2465, 2), (key2536, -2), (key2375, -2), (key2469, -2), (key2477, -6), (key2541, 2), (key2387, 2), (key2477, 2)]

def rawRow2403 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2399, -2), (key2403, 6), (key2500, 2), (key2469, 2), (key2465, 2), (key2536, -2), (key2469, -2), (key2375, -2), (key2477, -6), (key2541, 2), (key2477, 2), (key2387, 2)]

def rawRow2404 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2477, -2), (key2500, 6), (key2371, 2), (key2375, 2), (key2387, 2), (key2434, -2), (key2500, -2), (key2552, -2), (key2375, -6), (key2403, 2), (key2469, 2), (key2536, 2)]

def rawRow2405 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2477, -2), (key2500, 6), (key2375, 2), (key2371, 2), (key2387, 2), (key2434, -2), (key2552, -2), (key2500, -2), (key2375, -6), (key2403, 2), (key2536, 2), (key2469, 2)]

def rawRow2406 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2469, -2), (key2500, 6), (key2371, 2), (key2387, 2), (key2375, 2), (key2500, -2), (key2434, -2), (key2552, -2), (key2375, -6), (key2469, 2), (key2403, 2), (key2536, 2)]

def rawRow2407 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2469, -2), (key2500, 6), (key2387, 2), (key2371, 2), (key2375, 2), (key2500, -2), (key2552, -2), (key2434, -2), (key2375, -6), (key2469, 2), (key2536, 2), (key2403, 2)]

def rawRow2408 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2465, -2), (key2500, 6), (key2375, 2), (key2387, 2), (key2371, 2), (key2552, -2), (key2434, -2), (key2500, -2), (key2375, -6), (key2536, 2), (key2403, 2), (key2469, 2)]

def rawRow2409 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2465, -2), (key2500, 6), (key2387, 2), (key2375, 2), (key2371, 2), (key2552, -2), (key2500, -2), (key2434, -2), (key2375, -6), (key2536, 2), (key2469, 2), (key2403, 2)]

def rawRow2410 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2500, -2), (key2477, 6), (key2399, 2), (key2403, 2), (key2434, 2), (key2387, -2), (key2477, -2), (key2541, -2), (key2403, -6), (key2375, 2), (key2469, 2), (key2536, 2)]

def rawRow2411 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2500, -2), (key2477, 6), (key2403, 2), (key2399, 2), (key2434, 2), (key2387, -2), (key2541, -2), (key2477, -2), (key2403, -6), (key2375, 2), (key2536, 2), (key2469, 2)]

def rawRow2412 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2469, -2), (key2477, 6), (key2399, 2), (key2434, 2), (key2403, 2), (key2477, -2), (key2387, -2), (key2541, -2), (key2403, -6), (key2469, 2), (key2375, 2), (key2536, 2)]

def rawRow2413 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2469, -2), (key2477, 6), (key2434, 2), (key2399, 2), (key2403, 2), (key2477, -2), (key2541, -2), (key2387, -2), (key2403, -6), (key2469, 2), (key2536, 2), (key2375, 2)]

def rawRow2414 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2465, -2), (key2477, 6), (key2403, 2), (key2434, 2), (key2399, 2), (key2541, -2), (key2387, -2), (key2477, -2), (key2403, -6), (key2536, 2), (key2375, 2), (key2469, 2)]

def rawRow2415 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2465, -2), (key2477, 6), (key2434, 2), (key2403, 2), (key2399, 2), (key2541, -2), (key2477, -2), (key2387, -2), (key2403, -6), (key2536, 2), (key2469, 2), (key2375, 2)]

def rawRow2419 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2373, 6), (key2839, 2), (key2842, 2), (key2886, 2), (key2765, -2), (key2842, -2), (key2874, -2), (key2965, -6), (key2928, 2), (key2965, 2), (key2987, 2)]

def rawRow2420 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2386, -2), (key2373, 6), (key2842, 2), (key2839, 2), (key2886, 2), (key2765, -2), (key2874, -2), (key2842, -2), (key2965, -6), (key2928, 2), (key2987, 2), (key2965, 2)]

def rawRow2421 : Integer.Sparse Key := [(key2370, -2), (key2386, -2), (key2373, -2), (key2373, 6), (key2839, 2), (key2886, 2), (key2842, 2), (key2842, -2), (key2765, -2), (key2874, -2), (key2965, -6), (key2965, 2), (key2928, 2), (key2987, 2)]

def rawRow2422 : Integer.Sparse Key := [(key2386, -2), (key2370, -2), (key2373, -2), (key2373, 6), (key2886, 2), (key2839, 2), (key2842, 2), (key2842, -2), (key2874, -2), (key2765, -2), (key2965, -6), (key2965, 2), (key2987, 2), (key2928, 2)]

def rawRow2423 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2370, -2), (key2373, 6), (key2842, 2), (key2886, 2), (key2839, 2), (key2874, -2), (key2765, -2), (key2842, -2), (key2965, -6), (key2987, 2), (key2928, 2), (key2965, 2)]

def rawRow2424 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2370, -2), (key2373, 6), (key2886, 2), (key2842, 2), (key2839, 2), (key2874, -2), (key2842, -2), (key2765, -2), (key2965, -6), (key2987, 2), (key2965, 2), (key2928, 2)]

def rawRow2428 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2401, 6), (key2839, 2), (key2842, 2), (key2965, 2), (key2586, -2), (key2842, -2), (key2874, -2), (key2886, -6), (key2597, 2), (key2886, 2), (key2908, 2)]

def rawRow2429 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2433, -2), (key2401, 6), (key2842, 2), (key2839, 2), (key2965, 2), (key2586, -2), (key2874, -2), (key2842, -2), (key2886, -6), (key2597, 2), (key2908, 2), (key2886, 2)]

def rawRow2430 : Integer.Sparse Key := [(key2398, -2), (key2433, -2), (key2401, -2), (key2401, 6), (key2839, 2), (key2965, 2), (key2842, 2), (key2842, -2), (key2586, -2), (key2874, -2), (key2886, -6), (key2886, 2), (key2597, 2), (key2908, 2)]

def rawRow2431 : Integer.Sparse Key := [(key2433, -2), (key2398, -2), (key2401, -2), (key2401, 6), (key2965, 2), (key2839, 2), (key2842, 2), (key2842, -2), (key2874, -2), (key2586, -2), (key2886, -6), (key2886, 2), (key2908, 2), (key2597, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2432 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2398, -2), (key2401, 6), (key2842, 2), (key2965, 2), (key2839, 2), (key2874, -2), (key2586, -2), (key2842, -2), (key2886, -6), (key2908, 2), (key2597, 2), (key2886, 2)]

def rawRow2433 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2398, -2), (key2401, 6), (key2965, 2), (key2842, 2), (key2839, 2), (key2874, -2), (key2842, -2), (key2586, -2), (key2886, -6), (key2908, 2), (key2886, 2), (key2597, 2)]

def rawRow2434 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2476, -2), (key2499, 6), (key2370, 2), (key2373, 2), (key2386, 2), (key2928, -2), (key2965, -2), (key2987, -2), (key2586, -6), (key2765, 2), (key2842, 2), (key2874, 2)]

def rawRow2435 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2476, -2), (key2499, 6), (key2373, 2), (key2370, 2), (key2386, 2), (key2928, -2), (key2987, -2), (key2965, -2), (key2586, -6), (key2765, 2), (key2874, 2), (key2842, 2)]

def rawRow2436 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2467, -2), (key2499, 6), (key2370, 2), (key2386, 2), (key2373, 2), (key2965, -2), (key2928, -2), (key2987, -2), (key2586, -6), (key2842, 2), (key2765, 2), (key2874, 2)]

def rawRow2437 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2467, -2), (key2499, 6), (key2386, 2), (key2370, 2), (key2373, 2), (key2965, -2), (key2987, -2), (key2928, -2), (key2586, -6), (key2842, 2), (key2874, 2), (key2765, 2)]

def rawRow2438 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2464, -2), (key2499, 6), (key2373, 2), (key2386, 2), (key2370, 2), (key2987, -2), (key2928, -2), (key2965, -2), (key2586, -6), (key2874, 2), (key2765, 2), (key2842, 2)]

def rawRow2439 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2464, -2), (key2499, 6), (key2386, 2), (key2373, 2), (key2370, 2), (key2987, -2), (key2965, -2), (key2928, -2), (key2586, -6), (key2874, 2), (key2842, 2), (key2765, 2)]

def rawRow2440 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2499, -2), (key2476, 6), (key2398, 2), (key2401, 2), (key2433, 2), (key2597, -2), (key2886, -2), (key2908, -2), (key2765, -6), (key2586, 2), (key2842, 2), (key2874, 2)]

def rawRow2441 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2499, -2), (key2476, 6), (key2401, 2), (key2398, 2), (key2433, 2), (key2597, -2), (key2908, -2), (key2886, -2), (key2765, -6), (key2586, 2), (key2874, 2), (key2842, 2)]

def rawRow2442 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2467, -2), (key2476, 6), (key2398, 2), (key2433, 2), (key2401, 2), (key2886, -2), (key2597, -2), (key2908, -2), (key2765, -6), (key2842, 2), (key2586, 2), (key2874, 2)]

def rawRow2443 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2433, 2), (key2398, 2), (key2401, 2), (key2886, -2), (key2908, -2), (key2597, -2), (key2765, -6), (key2842, 2), (key2874, 2), (key2586, 2)]

def rawRow2444 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2464, -2), (key2476, 6), (key2401, 2), (key2433, 2), (key2398, 2), (key2908, -2), (key2597, -2), (key2886, -2), (key2765, -6), (key2874, 2), (key2586, 2), (key2842, 2)]

def rawRow2445 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2464, -2), (key2476, 6), (key2433, 2), (key2401, 2), (key2398, 2), (key2908, -2), (key2886, -2), (key2597, -2), (key2765, -6), (key2874, 2), (key2842, 2), (key2586, 2)]

def rawRow2476 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2189, -2), (key2175, 1), (key2179, 1), (key2175, 1), (key2189, 1), (key2179, 1), (key2189, 1), (key2275, 2), (key2275, 2), (key2289, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2327, -1), (key2328, -1), (key2327, -1), (key2333, -1), (key2328, -1), (key2333, -1), (key2327, 1), (key2330, 1), (key2327, 1), (key2333, 1), (key2330, 1), (key2333, 1)]

def rawRow2477 : Integer.Sparse Key := [(key2175, -2), (key2189, -2), (key2175, -2), (key2179, 1), (key2175, 1), (key2189, 1), (key2175, 1), (key2189, 1), (key2179, 1), (key2275, 2), (key2289, 2), (key2275, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2328, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2328, -1), (key2330, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2330, 1)]

def rawRow2478 : Integer.Sparse Key := [(key2189, -2), (key2175, -2), (key2175, -2), (key2189, 1), (key2189, 1), (key2179, 1), (key2179, 1), (key2175, 1), (key2175, 1), (key2289, 2), (key2275, 2), (key2275, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2333, -1), (key2333, -1), (key2328, -1), (key2328, -1), (key2327, -1), (key2327, -1), (key2333, 1), (key2333, 1), (key2330, 1), (key2330, 1), (key2327, 1), (key2327, 1)]

def rawRow2480 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2289, -2), (key2327, 1), (key2328, 1), (key2327, 1), (key2333, 1), (key2328, 1), (key2333, 1), (key2175, 2), (key2175, 2), (key2189, 2), (key2327, -1), (key2330, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2333, -1), (key2175, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2189, -1), (key2275, 1), (key2281, 1), (key2275, 1), (key2289, 1), (key2281, 1), (key2289, 1)]

def rawRow2481 : Integer.Sparse Key := [(key2275, -2), (key2289, -2), (key2275, -2), (key2328, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2328, 1), (key2175, 2), (key2189, 2), (key2175, 2), (key2330, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2179, -1), (key2175, -1), (key2189, -1), (key2175, -1), (key2189, -1), (key2179, -1), (key2281, 1), (key2275, 1), (key2289, 1), (key2275, 1), (key2289, 1), (key2281, 1)]

def rawRow2482 : Integer.Sparse Key := [(key2289, -2), (key2275, -2), (key2275, -2), (key2333, 1), (key2333, 1), (key2328, 1), (key2328, 1), (key2327, 1), (key2327, 1), (key2189, 2), (key2175, 2), (key2175, 2), (key2333, -1), (key2333, -1), (key2330, -1), (key2330, -1), (key2327, -1), (key2327, -1), (key2189, -1), (key2189, -1), (key2179, -1), (key2179, -1), (key2175, -1), (key2175, -1), (key2289, 1), (key2289, 1), (key2281, 1), (key2281, 1), (key2275, 1), (key2275, 1)]

def rawRow2483 : Integer.Sparse Key := [(key2082, -2), (key2328, -2), (key2328, -2), (key2078, 1), (key2078, 1), (key2275, 1), (key2275, 1), (key2327, 1), (key2327, 1), (key2087, 2), (key2330, 2), (key2330, 2), (key2078, -1), (key2078, -1), (key2175, -1), (key2175, -1), (key2327, -1), (key2327, -1), (key2087, -1), (key2087, -1), (key2281, -1), (key2281, -1), (key2330, -1), (key2330, -1), (key2082, 1), (key2082, 1), (key2179, 1), (key2179, 1), (key2328, 1), (key2328, 1)]

def rawRow2484 : Integer.Sparse Key := [(key2328, -2), (key2082, -2), (key2328, -2), (key2275, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2275, 1), (key2330, 2), (key2087, 2), (key2330, 2), (key2175, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2281, -1), (key2330, -1), (key2087, -1), (key2330, -1), (key2087, -1), (key2281, -1), (key2179, 1), (key2328, 1), (key2082, 1), (key2328, 1), (key2082, 1), (key2179, 1)]

def rawRow2485 : Integer.Sparse Key := [(key2328, -2), (key2328, -2), (key2082, -2), (key2327, 1), (key2275, 1), (key2327, 1), (key2078, 1), (key2275, 1), (key2078, 1), (key2330, 2), (key2330, 2), (key2087, 2), (key2327, -1), (key2175, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2078, -1), (key2330, -1), (key2281, -1), (key2330, -1), (key2087, -1), (key2281, -1), (key2087, -1), (key2328, 1), (key2179, 1), (key2328, 1), (key2082, 1), (key2179, 1), (key2082, 1)]

def rawRow2487 : Integer.Sparse Key := [(key2087, -2), (key2330, -2), (key2330, -2), (key2087, 1), (key2087, 1), (key2281, 1), (key2281, 1), (key2330, 1), (key2330, 1), (key2082, 2), (key2328, 2), (key2328, 2), (key2082, -1), (key2082, -1), (key2179, -1), (key2179, -1), (key2328, -1), (key2328, -1), (key2078, -1), (key2078, -1), (key2275, -1), (key2275, -1), (key2327, -1), (key2327, -1), (key2078, 1), (key2078, 1), (key2175, 1), (key2175, 1), (key2327, 1), (key2327, 1)]

def rawRow2488 : Integer.Sparse Key := [(key2330, -2), (key2087, -2), (key2330, -2), (key2281, 1), (key2330, 1), (key2087, 1), (key2330, 1), (key2087, 1), (key2281, 1), (key2328, 2), (key2082, 2), (key2328, 2), (key2179, -1), (key2328, -1), (key2082, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2275, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2275, -1), (key2175, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2175, 1)]

def rawRow2489 : Integer.Sparse Key := [(key2330, -2), (key2330, -2), (key2087, -2), (key2330, 1), (key2281, 1), (key2330, 1), (key2087, 1), (key2281, 1), (key2087, 1), (key2328, 2), (key2328, 2), (key2082, 2), (key2328, -1), (key2179, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2082, -1), (key2327, -1), (key2275, -1), (key2327, -1), (key2078, -1), (key2275, -1), (key2078, -1), (key2327, 1), (key2175, 1), (key2327, 1), (key2078, 1), (key2175, 1), (key2078, 1)]

def rawRow2490 : Integer.Sparse Key := [(key754, -6), (key754, 2), (key754, 2), (key755, 2), (key843, 6), (key843, -2), (key843, -2), (key844, -2), (key943, -2), (key943, -2), (key944, -2), (key943, 2), (key943, 2), (key945, 2)]

def rawRow2491 : Integer.Sparse Key := [(key754, -6), (key754, 2), (key755, 2), (key754, 2), (key843, 6), (key843, -2), (key844, -2), (key843, -2), (key943, -2), (key944, -2), (key943, -2), (key943, 2), (key945, 2), (key943, 2)]

def rawRow2492 : Integer.Sparse Key := [(key754, -6), (key755, 2), (key754, 2), (key754, 2), (key843, 6), (key844, -2), (key843, -2), (key843, -2), (key944, -2), (key943, -2), (key943, -2), (key945, 2), (key943, 2), (key943, 2)]

def rawRow2494 : Integer.Sparse Key := [(key843, -6), (key943, 2), (key943, 2), (key944, 2), (key754, 6), (key943, -2), (key943, -2), (key945, -2), (key754, -2), (key754, -2), (key755, -2), (key843, 2), (key843, 2), (key844, 2)]

def rawRow2495 : Integer.Sparse Key := [(key843, -6), (key943, 2), (key944, 2), (key943, 2), (key754, 6), (key943, -2), (key945, -2), (key943, -2), (key754, -2), (key755, -2), (key754, -2), (key843, 2), (key844, 2), (key843, 2)]

def rawRow2496 : Integer.Sparse Key := [(key843, -6), (key944, 2), (key943, 2), (key943, 2), (key754, 6), (key945, -2), (key943, -2), (key943, -2), (key755, -2), (key754, -2), (key754, -2), (key844, 2), (key843, 2), (key843, 2)]

def rawRow2497 : Integer.Sparse Key := [(key944, -6), (key843, 2), (key943, 2), (key943, 2), (key945, 6), (key754, -2), (key943, -2), (key943, -2), (key844, -2), (key945, -2), (key945, -2), (key755, 2), (key944, 2), (key944, 2)]

def rawRow2498 : Integer.Sparse Key := [(key944, -6), (key943, 2), (key843, 2), (key943, 2), (key945, 6), (key943, -2), (key754, -2), (key943, -2), (key945, -2), (key844, -2), (key945, -2), (key944, 2), (key755, 2), (key944, 2)]

def rawRow2499 : Integer.Sparse Key := [(key944, -6), (key943, 2), (key943, 2), (key843, 2), (key945, 6), (key943, -2), (key943, -2), (key754, -2), (key945, -2), (key945, -2), (key844, -2), (key944, 2), (key944, 2), (key755, 2)]

def rawRow2501 : Integer.Sparse Key := [(key945, -6), (key844, 2), (key945, 2), (key945, 2), (key944, 6), (key755, -2), (key944, -2), (key944, -2), (key843, -2), (key943, -2), (key943, -2), (key754, 2), (key943, 2), (key943, 2)]

def rawRow2502 : Integer.Sparse Key := [(key945, -6), (key945, 2), (key844, 2), (key945, 2), (key944, 6), (key944, -2), (key755, -2), (key944, -2), (key943, -2), (key843, -2), (key943, -2), (key943, 2), (key754, 2), (key943, 2)]

def rawRow2503 : Integer.Sparse Key := [(key945, -6), (key945, 2), (key945, 2), (key844, 2), (key944, 6), (key944, -2), (key944, -2), (key755, -2), (key943, -2), (key943, -2), (key843, -2), (key943, 2), (key943, 2), (key754, 2)]

def rawRow2504 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, -1), (key2176, -1), (key2174, -1), (key2187, -1), (key2176, -1), (key2187, -1), (key2274, -1), (key2276, -1), (key2274, -1), (key2279, -1), (key2276, -1), (key2279, -1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1)]

def rawRow2505 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 2), (key2174, 2), (key2176, 2), (key2176, -1), (key2174, -1), (key2187, -1), (key2174, -1), (key2187, -1), (key2176, -1), (key2276, -1), (key2274, -1), (key2279, -1), (key2274, -1), (key2279, -1), (key2276, -1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1)]

def rawRow2506 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, -1), (key2187, -1), (key2176, -1), (key2176, -1), (key2174, -1), (key2174, -1), (key2279, -1), (key2279, -1), (key2276, -1), (key2276, -1), (key2274, -1), (key2274, -1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1)]

def rawRow2508 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2077, 2), (key2079, 2), (key2079, 2), (key2274, -1), (key2276, -1), (key2274, -1), (key2287, -1), (key2276, -1), (key2287, -1), (key2077, -1), (key2079, -1), (key2077, -1), (key2085, -1), (key2079, -1), (key2085, -1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1)]

def rawRow2509 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2079, 2), (key2077, 2), (key2079, 2), (key2276, -1), (key2274, -1), (key2287, -1), (key2274, -1), (key2287, -1), (key2276, -1), (key2079, -1), (key2077, -1), (key2085, -1), (key2077, -1), (key2085, -1), (key2079, -1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1)]

def rawRow2510 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2079, 2), (key2079, 2), (key2077, 2), (key2287, -1), (key2287, -1), (key2276, -1), (key2276, -1), (key2274, -1), (key2274, -1), (key2085, -1), (key2085, -1), (key2079, -1), (key2079, -1), (key2077, -1), (key2077, -1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1)]

def rawRow2511 : Integer.Sparse Key := [(key2279, -2), (key2279, -2), (key2343, -2), (key2176, 1), (key2176, 1), (key2276, 1), (key2276, 1), (key2341, 1), (key2341, 1), (key2287, 2), (key2287, 2), (key2347, 2), (key2079, -1), (key2079, -1), (key2276, -1), (key2276, -1), (key2341, -1), (key2341, -1), (key2187, -1), (key2187, -1), (key2287, -1), (key2287, -1), (key2347, -1), (key2347, -1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1)]

def rawRow2512 : Integer.Sparse Key := [(key2279, -2), (key2343, -2), (key2279, -2), (key2276, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2176, 1), (key2276, 1), (key2287, 2), (key2347, 2), (key2287, 2), (key2276, -1), (key2341, -1), (key2079, -1), (key2341, -1), (key2079, -1), (key2276, -1), (key2287, -1), (key2347, -1), (key2187, -1), (key2347, -1), (key2187, -1), (key2287, -1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1)]

def rawRow2513 : Integer.Sparse Key := [(key2343, -2), (key2279, -2), (key2279, -2), (key2341, 1), (key2276, 1), (key2341, 1), (key2176, 1), (key2276, 1), (key2176, 1), (key2347, 2), (key2287, 2), (key2287, 2), (key2341, -1), (key2276, -1), (key2341, -1), (key2079, -1), (key2276, -1), (key2079, -1), (key2347, -1), (key2287, -1), (key2347, -1), (key2187, -1), (key2287, -1), (key2187, -1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1)]

def rawRow2515 : Integer.Sparse Key := [(key2287, -2), (key2287, -2), (key2347, -2), (key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2279, 2), (key2279, 2), (key2343, 2), (key2085, -1), (key2085, -1), (key2279, -1), (key2279, -1), (key2343, -1), (key2343, -1), (key2176, -1), (key2176, -1), (key2276, -1), (key2276, -1), (key2341, -1), (key2341, -1), (key2079, 1), (key2079, 1), (key2276, 1), (key2276, 1), (key2341, 1), (key2341, 1)]

def rawRow2516 : Integer.Sparse Key := [(key2287, -2), (key2347, -2), (key2287, -2), (key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 2), (key2343, 2), (key2279, 2), (key2279, -1), (key2343, -1), (key2085, -1), (key2343, -1), (key2085, -1), (key2279, -1), (key2276, -1), (key2341, -1), (key2176, -1), (key2341, -1), (key2176, -1), (key2276, -1), (key2276, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2276, 1)]

def rawRow2517 : Integer.Sparse Key := [(key2347, -2), (key2287, -2), (key2287, -2), (key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 2), (key2279, 2), (key2279, 2), (key2343, -1), (key2279, -1), (key2343, -1), (key2085, -1), (key2279, -1), (key2085, -1), (key2341, -1), (key2276, -1), (key2341, -1), (key2176, -1), (key2276, -1), (key2176, -1), (key2341, 1), (key2276, 1), (key2341, 1), (key2079, 1), (key2276, 1), (key2079, 1)]

def rawRow2518 : Integer.Sparse Key := [(key713, -2), (key715, -2), (key715, -2), (key715, 6), (key890, 2), (key892, 2), (key892, 2), (key892, -2), (key892, -2), (key914, -2), (key959, -6), (key959, 2), (key959, 2), (key966, 2)]

def rawRow2519 : Integer.Sparse Key := [(key715, -2), (key713, -2), (key715, -2), (key715, 6), (key892, 2), (key890, 2), (key892, 2), (key892, -2), (key914, -2), (key892, -2), (key959, -6), (key959, 2), (key966, 2), (key959, 2)]

def rawRow2520 : Integer.Sparse Key := [(key715, -2), (key715, -2), (key713, -2), (key715, 6), (key892, 2), (key892, 2), (key890, 2), (key914, -2), (key892, -2), (key892, -2), (key959, -6), (key966, 2), (key959, 2), (key959, 2)]

def rawRow2522 : Integer.Sparse Key := [(key890, -2), (key892, -2), (key892, -2), (key959, 6), (key713, 2), (key715, 2), (key715, 2), (key959, -2), (key959, -2), (key966, -2), (key715, -6), (key892, 2), (key892, 2), (key914, 2)]

def rawRow2523 : Integer.Sparse Key := [(key892, -2), (key890, -2), (key892, -2), (key959, 6), (key715, 2), (key713, 2), (key715, 2), (key959, -2), (key966, -2), (key959, -2), (key715, -6), (key892, 2), (key914, 2), (key892, 2)]

def rawRow2524 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key890, -2), (key959, 6), (key715, 2), (key715, 2), (key713, 2), (key966, -2), (key959, -2), (key959, -2), (key715, -6), (key914, 2), (key892, 2), (key892, 2)]

def rawRow2525 : Integer.Sparse Key := [(key892, -2), (key892, -2), (key959, -2), (key890, 6), (key914, 2), (key914, 2), (key966, 2), (key713, -2), (key890, -2), (key890, -2), (key914, -6), (key715, 2), (key892, 2), (key892, 2)]

def rawRow2526 : Integer.Sparse Key := [(key892, -2), (key959, -2), (key892, -2), (key890, 6), (key914, 2), (key966, 2), (key914, 2), (key890, -2), (key713, -2), (key890, -2), (key914, -6), (key892, 2), (key715, 2), (key892, 2)]

def rawRow2527 : Integer.Sparse Key := [(key959, -2), (key892, -2), (key892, -2), (key890, 6), (key966, 2), (key914, 2), (key914, 2), (key890, -2), (key890, -2), (key713, -2), (key914, -6), (key892, 2), (key892, 2), (key715, 2)]

def rawRow2529 : Integer.Sparse Key := [(key914, -2), (key914, -2), (key966, -2), (key914, 6), (key892, 2), (key892, 2), (key959, 2), (key715, -2), (key892, -2), (key892, -2), (key890, -6), (key713, 2), (key890, 2), (key890, 2)]

def rawRow2530 : Integer.Sparse Key := [(key914, -2), (key966, -2), (key914, -2), (key914, 6), (key892, 2), (key959, 2), (key892, 2), (key892, -2), (key715, -2), (key892, -2), (key890, -6), (key890, 2), (key713, 2), (key890, 2)]

def rawRow2531 : Integer.Sparse Key := [(key966, -2), (key914, -2), (key914, -2), (key914, 6), (key959, 2), (key892, 2), (key892, 2), (key892, -2), (key892, -2), (key715, -2), (key890, -6), (key890, 2), (key890, 2), (key713, 2)]

def rawRow2532 : Integer.Sparse Key := [(key2098, -6), (key2098, 2), (key2098, 2), (key2099, 2), (key2203, 6), (key2203, -2), (key2203, -2), (key2206, -2), (key2317, -2), (key2317, -2), (key2318, -2), (key2317, 2), (key2317, 2), (key2321, 2)]

def rawRow2533 : Integer.Sparse Key := [(key2098, -6), (key2098, 2), (key2099, 2), (key2098, 2), (key2203, 6), (key2203, -2), (key2206, -2), (key2203, -2), (key2317, -2), (key2318, -2), (key2317, -2), (key2317, 2), (key2321, 2), (key2317, 2)]

def rawRow2534 : Integer.Sparse Key := [(key2098, -6), (key2099, 2), (key2098, 2), (key2098, 2), (key2203, 6), (key2206, -2), (key2203, -2), (key2203, -2), (key2318, -2), (key2317, -2), (key2317, -2), (key2321, 2), (key2317, 2), (key2317, 2)]

def rawRow2536 : Integer.Sparse Key := [(key2203, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2098, 6), (key2317, -2), (key2317, -2), (key2321, -2), (key2098, -2), (key2098, -2), (key2099, -2), (key2203, 2), (key2203, 2), (key2206, 2)]

def rawRow2537 : Integer.Sparse Key := [(key2203, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2098, 6), (key2317, -2), (key2321, -2), (key2317, -2), (key2098, -2), (key2099, -2), (key2098, -2), (key2203, 2), (key2206, 2), (key2203, 2)]

def rawRow2538 : Integer.Sparse Key := [(key2203, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2098, 6), (key2321, -2), (key2317, -2), (key2317, -2), (key2099, -2), (key2098, -2), (key2098, -2), (key2206, 2), (key2203, 2), (key2203, 2)]

def rawRow2539 : Integer.Sparse Key := [(key2318, -6), (key2203, 2), (key2317, 2), (key2317, 2), (key2321, 6), (key2098, -2), (key2317, -2), (key2317, -2), (key2206, -2), (key2321, -2), (key2321, -2), (key2099, 2), (key2318, 2), (key2318, 2)]

def rawRow2540 : Integer.Sparse Key := [(key2318, -6), (key2317, 2), (key2203, 2), (key2317, 2), (key2321, 6), (key2317, -2), (key2098, -2), (key2317, -2), (key2321, -2), (key2206, -2), (key2321, -2), (key2318, 2), (key2099, 2), (key2318, 2)]

def rawRow2541 : Integer.Sparse Key := [(key2318, -6), (key2317, 2), (key2317, 2), (key2203, 2), (key2321, 6), (key2317, -2), (key2317, -2), (key2098, -2), (key2321, -2), (key2321, -2), (key2206, -2), (key2318, 2), (key2318, 2), (key2099, 2)]

def rawRow2543 : Integer.Sparse Key := [(key2321, -6), (key2206, 2), (key2321, 2), (key2321, 2), (key2318, 6), (key2099, -2), (key2318, -2), (key2318, -2), (key2203, -2), (key2317, -2), (key2317, -2), (key2098, 2), (key2317, 2), (key2317, 2)]

def rawRow2544 : Integer.Sparse Key := [(key2321, -6), (key2321, 2), (key2206, 2), (key2321, 2), (key2318, 6), (key2318, -2), (key2099, -2), (key2318, -2), (key2317, -2), (key2203, -2), (key2317, -2), (key2317, 2), (key2098, 2), (key2317, 2)]

def rawRow2545 : Integer.Sparse Key := [(key2321, -6), (key2321, 2), (key2321, 2), (key2206, 2), (key2318, 6), (key2318, -2), (key2318, -2), (key2099, -2), (key2317, -2), (key2317, -2), (key2203, -2), (key2317, 2), (key2317, 2), (key2098, 2)]

def rawRow2546 : Integer.Sparse Key := [(key817, -1), (key818, -1), (key817, -1), (key825, -1), (key818, -1), (key825, -1), (key818, 2), (key818, 2), (key825, 2), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1), (key898, -1), (key902, -1), (key898, -1), (key908, -1), (key902, -1), (key908, -1), (key960, -2), (key960, -2), (key964, -2), (key960, 1), (key962, 1), (key960, 1), (key964, 1), (key962, 1), (key964, 1)]

def rawRow2547 : Integer.Sparse Key := [(key818, -1), (key817, -1), (key825, -1), (key817, -1), (key825, -1), (key818, -1), (key818, 2), (key825, 2), (key818, 2), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1), (key902, -1), (key898, -1), (key908, -1), (key898, -1), (key908, -1), (key902, -1), (key960, -2), (key964, -2), (key960, -2), (key962, 1), (key960, 1), (key964, 1), (key960, 1), (key964, 1), (key962, 1)]

def rawRow2548 : Integer.Sparse Key := [(key825, -1), (key825, -1), (key818, -1), (key818, -1), (key817, -1), (key817, -1), (key825, 2), (key818, 2), (key818, 2), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, -1), (key908, -1), (key902, -1), (key902, -1), (key898, -1), (key898, -1), (key964, -2), (key960, -2), (key960, -2), (key964, 1), (key964, 1), (key962, 1), (key962, 1), (key960, 1), (key960, 1)]

def rawRow2550 : Integer.Sparse Key := [(key897, -1), (key898, -1), (key897, -1), (key908, -1), (key898, -1), (key908, -1), (key960, 2), (key960, 2), (key964, 2), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1), (key960, -1), (key962, -1), (key960, -1), (key964, -1), (key962, -1), (key964, -1), (key818, -2), (key818, -2), (key825, -2), (key898, 1), (key902, 1), (key898, 1), (key908, 1), (key902, 1), (key908, 1)]

def rawRow2551 : Integer.Sparse Key := [(key898, -1), (key897, -1), (key908, -1), (key897, -1), (key908, -1), (key898, -1), (key960, 2), (key964, 2), (key960, 2), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1), (key962, -1), (key960, -1), (key964, -1), (key960, -1), (key964, -1), (key962, -1), (key818, -2), (key825, -2), (key818, -2), (key902, 1), (key898, 1), (key908, 1), (key898, 1), (key908, 1), (key902, 1)]

def rawRow2552 : Integer.Sparse Key := [(key908, -1), (key908, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key964, 2), (key960, 2), (key960, 2), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1), (key964, -1), (key964, -1), (key962, -1), (key962, -1), (key960, -1), (key960, -1), (key825, -2), (key818, -2), (key818, -2), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1)]

def rawRow2553 : Integer.Sparse Key := [(key738, -1), (key738, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key737, 2), (key897, 2), (key897, 2), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1), (key737, -1), (key737, -1), (key817, -1), (key817, -1), (key897, -1), (key897, -1), (key743, -2), (key902, -2), (key902, -2), (key738, 1), (key738, 1), (key818, 1), (key818, 1), (key898, 1), (key898, 1)]

def rawRow2554 : Integer.Sparse Key := [(key898, -1), (key960, -1), (key738, -1), (key960, -1), (key738, -1), (key898, -1), (key897, 2), (key737, 2), (key897, 2), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1), (key817, -1), (key897, -1), (key737, -1), (key897, -1), (key737, -1), (key817, -1), (key902, -2), (key743, -2), (key902, -2), (key818, 1), (key898, 1), (key738, 1), (key898, 1), (key738, 1), (key818, 1)]

def rawRow2555 : Integer.Sparse Key := [(key960, -1), (key898, -1), (key960, -1), (key738, -1), (key898, -1), (key738, -1), (key897, 2), (key897, 2), (key737, 2), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1), (key897, -1), (key817, -1), (key897, -1), (key737, -1), (key817, -1), (key737, -1), (key902, -2), (key902, -2), (key743, -2), (key898, 1), (key818, 1), (key898, 1), (key738, 1), (key818, 1), (key738, 1)]

def rawRow2557 : Integer.Sparse Key := [(key743, -1), (key743, -1), (key902, -1), (key902, -1), (key962, -1), (key962, -1), (key743, 2), (key902, 2), (key902, 2), (key738, 1), (key738, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1), (key738, -1), (key738, -1), (key818, -1), (key818, -1), (key898, -1), (key898, -1), (key737, -2), (key897, -2), (key897, -2), (key737, 1), (key737, 1), (key817, 1), (key817, 1), (key897, 1), (key897, 1)]

def rawRow2558 : Integer.Sparse Key := [(key902, -1), (key962, -1), (key743, -1), (key962, -1), (key743, -1), (key902, -1), (key902, 2), (key743, 2), (key902, 2), (key898, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key898, 1), (key818, -1), (key898, -1), (key738, -1), (key898, -1), (key738, -1), (key818, -1), (key897, -2), (key737, -2), (key897, -2), (key817, 1), (key897, 1), (key737, 1), (key897, 1), (key737, 1), (key817, 1)]

def rawRow2559 : Integer.Sparse Key := [(key962, -1), (key902, -1), (key962, -1), (key743, -1), (key902, -1), (key743, -1), (key902, 2), (key902, 2), (key743, 2), (key960, 1), (key898, 1), (key960, 1), (key738, 1), (key898, 1), (key738, 1), (key898, -1), (key818, -1), (key898, -1), (key738, -1), (key818, -1), (key738, -1), (key897, -2), (key897, -2), (key737, -2), (key897, 1), (key817, 1), (key897, 1), (key737, 1), (key817, 1), (key737, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2560 : Integer.Sparse Key := [(key2182, -2), (key2185, -2), (key2185, -2), (key2183, 2), (key2185, 2), (key2185, 2), (key2284, 2), (key2285, 2), (key2285, 2), (key2285, -6), (key2345, -2), (key2346, -2), (key2346, -2), (key2346, 6)]

def rawRow2561 : Integer.Sparse Key := [(key2185, -2), (key2182, -2), (key2185, -2), (key2185, 2), (key2183, 2), (key2185, 2), (key2285, 2), (key2284, 2), (key2285, 2), (key2285, -6), (key2346, -2), (key2345, -2), (key2346, -2), (key2346, 6)]

def rawRow2562 : Integer.Sparse Key := [(key2185, -2), (key2185, -2), (key2182, -2), (key2185, 2), (key2185, 2), (key2183, 2), (key2285, 2), (key2285, 2), (key2284, 2), (key2285, -6), (key2346, -2), (key2346, -2), (key2345, -2), (key2346, 6)]

def rawRow2564 : Integer.Sparse Key := [(key2284, -2), (key2285, -2), (key2285, -2), (key2345, 2), (key2346, 2), (key2346, 2), (key2182, 2), (key2185, 2), (key2185, 2), (key2346, -6), (key2183, -2), (key2185, -2), (key2185, -2), (key2285, 6)]

def rawRow2565 : Integer.Sparse Key := [(key2285, -2), (key2284, -2), (key2285, -2), (key2346, 2), (key2345, 2), (key2346, 2), (key2185, 2), (key2182, 2), (key2185, 2), (key2346, -6), (key2185, -2), (key2183, -2), (key2185, -2), (key2285, 6)]

def rawRow2566 : Integer.Sparse Key := [(key2285, -2), (key2285, -2), (key2284, -2), (key2346, 2), (key2346, 2), (key2345, 2), (key2185, 2), (key2185, 2), (key2182, 2), (key2346, -6), (key2185, -2), (key2185, -2), (key2183, -2), (key2285, 6)]

def rawRow2567 : Integer.Sparse Key := [(key2183, -2), (key2183, -2), (key2345, -2), (key2182, 2), (key2182, 2), (key2284, 2), (key2185, 2), (key2185, 2), (key2346, 2), (key2182, -6), (key2185, -2), (key2185, -2), (key2285, -2), (key2183, 6)]

def rawRow2568 : Integer.Sparse Key := [(key2183, -2), (key2345, -2), (key2183, -2), (key2182, 2), (key2284, 2), (key2182, 2), (key2185, 2), (key2346, 2), (key2185, 2), (key2182, -6), (key2185, -2), (key2285, -2), (key2185, -2), (key2183, 6)]

def rawRow2569 : Integer.Sparse Key := [(key2345, -2), (key2183, -2), (key2183, -2), (key2284, 2), (key2182, 2), (key2182, 2), (key2346, 2), (key2185, 2), (key2185, 2), (key2182, -6), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, 6)]

def rawRow2571 : Integer.Sparse Key := [(key2185, -2), (key2185, -2), (key2346, -2), (key2185, 2), (key2185, 2), (key2285, 2), (key2183, 2), (key2183, 2), (key2345, 2), (key2183, -6), (key2182, -2), (key2182, -2), (key2284, -2), (key2182, 6)]

def rawRow2572 : Integer.Sparse Key := [(key2185, -2), (key2346, -2), (key2185, -2), (key2185, 2), (key2285, 2), (key2185, 2), (key2183, 2), (key2345, 2), (key2183, 2), (key2183, -6), (key2182, -2), (key2284, -2), (key2182, -2), (key2182, 6)]

def rawRow2573 : Integer.Sparse Key := [(key2346, -2), (key2185, -2), (key2185, -2), (key2285, 2), (key2185, 2), (key2185, 2), (key2345, 2), (key2183, 2), (key2183, 2), (key2183, -6), (key2284, -2), (key2182, -2), (key2182, -2), (key2182, 6)]

def rawRow2574 : Integer.Sparse Key := [(key737, -2), (key738, -2), (key738, -2), (key737, 1), (key738, 1), (key737, 1), (key743, 1), (key738, 1), (key743, 1), (key817, 2), (key818, 2), (key818, 2), (key817, -1), (key818, -1), (key817, -1), (key825, -1), (key818, -1), (key825, -1), (key897, -1), (key898, -1), (key897, -1), (key902, -1), (key898, -1), (key902, -1), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1)]

def rawRow2575 : Integer.Sparse Key := [(key738, -2), (key737, -2), (key738, -2), (key738, 1), (key737, 1), (key743, 1), (key737, 1), (key743, 1), (key738, 1), (key818, 2), (key817, 2), (key818, 2), (key818, -1), (key817, -1), (key825, -1), (key817, -1), (key825, -1), (key818, -1), (key898, -1), (key897, -1), (key902, -1), (key897, -1), (key902, -1), (key898, -1), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1)]

def rawRow2576 : Integer.Sparse Key := [(key738, -2), (key738, -2), (key737, -2), (key743, 1), (key743, 1), (key738, 1), (key738, 1), (key737, 1), (key737, 1), (key818, 2), (key818, 2), (key817, 2), (key825, -1), (key825, -1), (key818, -1), (key818, -1), (key817, -1), (key817, -1), (key902, -1), (key902, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1)]

def rawRow2578 : Integer.Sparse Key := [(key817, -2), (key818, -2), (key818, -2), (key897, 1), (key898, 1), (key897, 1), (key902, 1), (key898, 1), (key902, 1), (key737, 2), (key738, 2), (key738, 2), (key897, -1), (key898, -1), (key897, -1), (key908, -1), (key898, -1), (key908, -1), (key737, -1), (key738, -1), (key737, -1), (key743, -1), (key738, -1), (key743, -1), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1)]

def rawRow2579 : Integer.Sparse Key := [(key818, -2), (key817, -2), (key818, -2), (key898, 1), (key897, 1), (key902, 1), (key897, 1), (key902, 1), (key898, 1), (key738, 2), (key737, 2), (key738, 2), (key898, -1), (key897, -1), (key908, -1), (key897, -1), (key908, -1), (key898, -1), (key738, -1), (key737, -1), (key743, -1), (key737, -1), (key743, -1), (key738, -1), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1)]

def rawRow2580 : Integer.Sparse Key := [(key818, -2), (key818, -2), (key817, -2), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key738, 2), (key738, 2), (key737, 2), (key908, -1), (key908, -1), (key898, -1), (key898, -1), (key897, -1), (key897, -1), (key743, -1), (key743, -1), (key738, -1), (key738, -1), (key737, -1), (key737, -1), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1)]

def rawRow2581 : Integer.Sparse Key := [(key902, -2), (key902, -2), (key962, -2), (key818, 1), (key818, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1), (key908, 2), (key908, 2), (key964, 2), (key738, -1), (key738, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key825, -1), (key825, -1), (key908, -1), (key908, -1), (key964, -1), (key964, -1), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1)]

def rawRow2582 : Integer.Sparse Key := [(key902, -2), (key962, -2), (key902, -2), (key898, 1), (key960, 1), (key818, 1), (key960, 1), (key818, 1), (key898, 1), (key908, 2), (key964, 2), (key908, 2), (key898, -1), (key960, -1), (key738, -1), (key960, -1), (key738, -1), (key898, -1), (key908, -1), (key964, -1), (key825, -1), (key964, -1), (key825, -1), (key908, -1), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1)]

def rawRow2583 : Integer.Sparse Key := [(key962, -2), (key902, -2), (key902, -2), (key960, 1), (key898, 1), (key960, 1), (key818, 1), (key898, 1), (key818, 1), (key964, 2), (key908, 2), (key908, 2), (key960, -1), (key898, -1), (key960, -1), (key738, -1), (key898, -1), (key738, -1), (key964, -1), (key908, -1), (key964, -1), (key825, -1), (key908, -1), (key825, -1), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1)]

def rawRow2585 : Integer.Sparse Key := [(key908, -2), (key908, -2), (key964, -2), (key825, 1), (key825, 1), (key908, 1), (key908, 1), (key964, 1), (key964, 1), (key902, 2), (key902, 2), (key962, 2), (key743, -1), (key743, -1), (key902, -1), (key902, -1), (key962, -1), (key962, -1), (key818, -1), (key818, -1), (key898, -1), (key898, -1), (key960, -1), (key960, -1), (key738, 1), (key738, 1), (key898, 1), (key898, 1), (key960, 1), (key960, 1)]

def rawRow2586 : Integer.Sparse Key := [(key908, -2), (key964, -2), (key908, -2), (key908, 1), (key964, 1), (key825, 1), (key964, 1), (key825, 1), (key908, 1), (key902, 2), (key962, 2), (key902, 2), (key902, -1), (key962, -1), (key743, -1), (key962, -1), (key743, -1), (key902, -1), (key898, -1), (key960, -1), (key818, -1), (key960, -1), (key818, -1), (key898, -1), (key898, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key898, 1)]

def rawRow2587 : Integer.Sparse Key := [(key964, -2), (key908, -2), (key908, -2), (key964, 1), (key908, 1), (key964, 1), (key825, 1), (key908, 1), (key825, 1), (key962, 2), (key902, 2), (key902, 2), (key962, -1), (key902, -1), (key962, -1), (key743, -1), (key902, -1), (key743, -1), (key960, -1), (key898, -1), (key960, -1), (key818, -1), (key898, -1), (key818, -1), (key960, 1), (key898, 1), (key960, 1), (key738, 1), (key898, 1), (key738, 1)]

def rawRow2588 : Integer.Sparse Key := [(key721, -2), (key722, -2), (key722, -2), (key722, 6), (key921, 2), (key922, 2), (key922, 2), (key922, -2), (key922, -2), (key939, -2), (key959, -6), (key959, 2), (key959, 2), (key966, 2)]

def rawRow2589 : Integer.Sparse Key := [(key722, -2), (key721, -2), (key722, -2), (key722, 6), (key922, 2), (key921, 2), (key922, 2), (key922, -2), (key939, -2), (key922, -2), (key959, -6), (key959, 2), (key966, 2), (key959, 2)]

def rawRow2590 : Integer.Sparse Key := [(key722, -2), (key722, -2), (key721, -2), (key722, 6), (key922, 2), (key922, 2), (key921, 2), (key939, -2), (key922, -2), (key922, -2), (key959, -6), (key966, 2), (key959, 2), (key959, 2)]

def rawRow2592 : Integer.Sparse Key := [(key921, -2), (key922, -2), (key922, -2), (key959, 6), (key721, 2), (key722, 2), (key722, 2), (key959, -2), (key959, -2), (key966, -2), (key722, -6), (key922, 2), (key922, 2), (key939, 2)]

def rawRow2593 : Integer.Sparse Key := [(key922, -2), (key921, -2), (key922, -2), (key959, 6), (key722, 2), (key721, 2), (key722, 2), (key959, -2), (key966, -2), (key959, -2), (key722, -6), (key922, 2), (key939, 2), (key922, 2)]

def rawRow2594 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key921, -2), (key959, 6), (key722, 2), (key722, 2), (key721, 2), (key966, -2), (key959, -2), (key959, -2), (key722, -6), (key939, 2), (key922, 2), (key922, 2)]

def rawRow2595 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key959, -2), (key921, 6), (key939, 2), (key939, 2), (key966, 2), (key721, -2), (key921, -2), (key921, -2), (key939, -6), (key722, 2), (key922, 2), (key922, 2)]

def rawRow2596 : Integer.Sparse Key := [(key922, -2), (key959, -2), (key922, -2), (key921, 6), (key939, 2), (key966, 2), (key939, 2), (key921, -2), (key721, -2), (key921, -2), (key939, -6), (key922, 2), (key722, 2), (key922, 2)]

def rawRow2597 : Integer.Sparse Key := [(key959, -2), (key922, -2), (key922, -2), (key921, 6), (key966, 2), (key939, 2), (key939, 2), (key921, -2), (key921, -2), (key721, -2), (key939, -6), (key922, 2), (key922, 2), (key722, 2)]

def rawRow2599 : Integer.Sparse Key := [(key939, -2), (key939, -2), (key966, -2), (key939, 6), (key922, 2), (key922, 2), (key959, 2), (key722, -2), (key922, -2), (key922, -2), (key921, -6), (key721, 2), (key921, 2), (key921, 2)]

def rawRow2600 : Integer.Sparse Key := [(key939, -2), (key966, -2), (key939, -2), (key939, 6), (key922, 2), (key959, 2), (key922, 2), (key922, -2), (key722, -2), (key922, -2), (key921, -6), (key921, 2), (key721, 2), (key921, 2)]

def rawRow2601 : Integer.Sparse Key := [(key966, -2), (key939, -2), (key939, -2), (key939, 6), (key959, 2), (key922, 2), (key922, 2), (key922, -2), (key922, -2), (key722, -2), (key921, -6), (key921, 2), (key921, 2), (key721, 2)]

def rawRow2602 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2087, -2), (key2078, 1), (key2082, 1), (key2078, 1), (key2087, 1), (key2082, 1), (key2087, 1), (key2275, 2), (key2275, 2), (key2281, 2), (key2275, -1), (key2281, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2289, -1), (key2327, -1), (key2328, -1), (key2327, -1), (key2330, -1), (key2328, -1), (key2330, -1), (key2327, 1), (key2330, 1), (key2327, 1), (key2333, 1), (key2330, 1), (key2333, 1)]

def rawRow2603 : Integer.Sparse Key := [(key2078, -2), (key2087, -2), (key2078, -2), (key2082, 1), (key2078, 1), (key2087, 1), (key2078, 1), (key2087, 1), (key2082, 1), (key2275, 2), (key2281, 2), (key2275, 2), (key2281, -1), (key2275, -1), (key2289, -1), (key2275, -1), (key2289, -1), (key2281, -1), (key2328, -1), (key2327, -1), (key2330, -1), (key2327, -1), (key2330, -1), (key2328, -1), (key2330, 1), (key2327, 1), (key2333, 1), (key2327, 1), (key2333, 1), (key2330, 1)]

def rawRow2604 : Integer.Sparse Key := [(key2087, -2), (key2078, -2), (key2078, -2), (key2087, 1), (key2087, 1), (key2082, 1), (key2082, 1), (key2078, 1), (key2078, 1), (key2281, 2), (key2275, 2), (key2275, 2), (key2289, -1), (key2289, -1), (key2281, -1), (key2281, -1), (key2275, -1), (key2275, -1), (key2330, -1), (key2330, -1), (key2328, -1), (key2328, -1), (key2327, -1), (key2327, -1), (key2333, 1), (key2333, 1), (key2330, 1), (key2330, 1), (key2327, 1), (key2327, 1)]

def rawRow2606 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2281, -2), (key2327, 1), (key2328, 1), (key2327, 1), (key2330, 1), (key2328, 1), (key2330, 1), (key2078, 2), (key2078, 2), (key2087, 2), (key2327, -1), (key2330, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2333, -1), (key2078, -1), (key2082, -1), (key2078, -1), (key2087, -1), (key2082, -1), (key2087, -1), (key2275, 1), (key2281, 1), (key2275, 1), (key2289, 1), (key2281, 1), (key2289, 1)]

def rawRow2607 : Integer.Sparse Key := [(key2275, -2), (key2281, -2), (key2275, -2), (key2328, 1), (key2327, 1), (key2330, 1), (key2327, 1), (key2330, 1), (key2328, 1), (key2078, 2), (key2087, 2), (key2078, 2), (key2330, -1), (key2327, -1), (key2333, -1), (key2327, -1), (key2333, -1), (key2330, -1), (key2082, -1), (key2078, -1), (key2087, -1), (key2078, -1), (key2087, -1), (key2082, -1), (key2281, 1), (key2275, 1), (key2289, 1), (key2275, 1), (key2289, 1), (key2281, 1)]

def rawRow2608 : Integer.Sparse Key := [(key2281, -2), (key2275, -2), (key2275, -2), (key2330, 1), (key2330, 1), (key2328, 1), (key2328, 1), (key2327, 1), (key2327, 1), (key2087, 2), (key2078, 2), (key2078, 2), (key2333, -1), (key2333, -1), (key2330, -1), (key2330, -1), (key2327, -1), (key2327, -1), (key2087, -1), (key2087, -1), (key2082, -1), (key2082, -1), (key2078, -1), (key2078, -1), (key2289, 1), (key2289, 1), (key2281, 1), (key2281, 1), (key2275, 1), (key2275, 1)]

def rawRow2609 : Integer.Sparse Key := [(key2179, -2), (key2328, -2), (key2328, -2), (key2175, 1), (key2175, 1), (key2275, 1), (key2275, 1), (key2327, 1), (key2327, 1), (key2189, 2), (key2333, 2), (key2333, 2), (key2078, -1), (key2078, -1), (key2175, -1), (key2175, -1), (key2327, -1), (key2327, -1), (key2189, -1), (key2189, -1), (key2289, -1), (key2289, -1), (key2333, -1), (key2333, -1), (key2082, 1), (key2082, 1), (key2179, 1), (key2179, 1), (key2328, 1), (key2328, 1)]

def rawRow2610 : Integer.Sparse Key := [(key2328, -2), (key2179, -2), (key2328, -2), (key2275, 1), (key2327, 1), (key2175, 1), (key2327, 1), (key2175, 1), (key2275, 1), (key2333, 2), (key2189, 2), (key2333, 2), (key2175, -1), (key2327, -1), (key2078, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2289, -1), (key2333, -1), (key2189, -1), (key2333, -1), (key2189, -1), (key2289, -1), (key2179, 1), (key2328, 1), (key2082, 1), (key2328, 1), (key2082, 1), (key2179, 1)]

def rawRow2611 : Integer.Sparse Key := [(key2328, -2), (key2328, -2), (key2179, -2), (key2327, 1), (key2275, 1), (key2327, 1), (key2175, 1), (key2275, 1), (key2175, 1), (key2333, 2), (key2333, 2), (key2189, 2), (key2327, -1), (key2175, -1), (key2327, -1), (key2078, -1), (key2175, -1), (key2078, -1), (key2333, -1), (key2289, -1), (key2333, -1), (key2189, -1), (key2289, -1), (key2189, -1), (key2328, 1), (key2179, 1), (key2328, 1), (key2082, 1), (key2179, 1), (key2082, 1)]

def rawRow2613 : Integer.Sparse Key := [(key2189, -2), (key2333, -2), (key2333, -2), (key2189, 1), (key2189, 1), (key2289, 1), (key2289, 1), (key2333, 1), (key2333, 1), (key2179, 2), (key2328, 2), (key2328, 2), (key2082, -1), (key2082, -1), (key2179, -1), (key2179, -1), (key2328, -1), (key2328, -1), (key2175, -1), (key2175, -1), (key2275, -1), (key2275, -1), (key2327, -1), (key2327, -1), (key2078, 1), (key2078, 1), (key2175, 1), (key2175, 1), (key2327, 1), (key2327, 1)]

def rawRow2614 : Integer.Sparse Key := [(key2333, -2), (key2189, -2), (key2333, -2), (key2289, 1), (key2333, 1), (key2189, 1), (key2333, 1), (key2189, 1), (key2289, 1), (key2328, 2), (key2179, 2), (key2328, 2), (key2179, -1), (key2328, -1), (key2082, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2275, -1), (key2327, -1), (key2175, -1), (key2327, -1), (key2175, -1), (key2275, -1), (key2175, 1), (key2327, 1), (key2078, 1), (key2327, 1), (key2078, 1), (key2175, 1)]

def rawRow2615 : Integer.Sparse Key := [(key2333, -2), (key2333, -2), (key2189, -2), (key2333, 1), (key2289, 1), (key2333, 1), (key2189, 1), (key2289, 1), (key2189, 1), (key2328, 2), (key2328, 2), (key2179, 2), (key2328, -1), (key2179, -1), (key2328, -1), (key2082, -1), (key2179, -1), (key2082, -1), (key2327, -1), (key2275, -1), (key2327, -1), (key2175, -1), (key2275, -1), (key2175, -1), (key2327, 1), (key2175, 1), (key2327, 1), (key2078, 1), (key2175, 1), (key2078, 1)]

def rawRow2616 : Integer.Sparse Key := [(key1998, -2), (key2000, -2), (key2000, -2), (key2000, 6), (key2267, 2), (key2269, 2), (key2269, 2), (key2269, -2), (key2269, -2), (key2292, -2), (key2340, -6), (key2340, 2), (key2340, 2), (key2349, 2)]

def rawRow2617 : Integer.Sparse Key := [(key2000, -2), (key1998, -2), (key2000, -2), (key2000, 6), (key2269, 2), (key2267, 2), (key2269, 2), (key2269, -2), (key2292, -2), (key2269, -2), (key2340, -6), (key2340, 2), (key2349, 2), (key2340, 2)]

def rawRow2618 : Integer.Sparse Key := [(key2000, -2), (key2000, -2), (key1998, -2), (key2000, 6), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, -2), (key2269, -2), (key2269, -2), (key2340, -6), (key2349, 2), (key2340, 2), (key2340, 2)]

def rawRow2620 : Integer.Sparse Key := [(key2267, -2), (key2269, -2), (key2269, -2), (key2340, 6), (key1998, 2), (key2000, 2), (key2000, 2), (key2340, -2), (key2340, -2), (key2349, -2), (key2000, -6), (key2269, 2), (key2269, 2), (key2292, 2)]

def rawRow2621 : Integer.Sparse Key := [(key2269, -2), (key2267, -2), (key2269, -2), (key2340, 6), (key2000, 2), (key1998, 2), (key2000, 2), (key2340, -2), (key2349, -2), (key2340, -2), (key2000, -6), (key2269, 2), (key2292, 2), (key2269, 2)]

def rawRow2622 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2267, -2), (key2340, 6), (key2000, 2), (key2000, 2), (key1998, 2), (key2349, -2), (key2340, -2), (key2340, -2), (key2000, -6), (key2292, 2), (key2269, 2), (key2269, 2)]

def rawRow2623 : Integer.Sparse Key := [(key2269, -2), (key2269, -2), (key2340, -2), (key2267, 6), (key2292, 2), (key2292, 2), (key2349, 2), (key1998, -2), (key2267, -2), (key2267, -2), (key2292, -6), (key2000, 2), (key2269, 2), (key2269, 2)]

def rawRow2624 : Integer.Sparse Key := [(key2269, -2), (key2340, -2), (key2269, -2), (key2267, 6), (key2292, 2), (key2349, 2), (key2292, 2), (key2267, -2), (key1998, -2), (key2267, -2), (key2292, -6), (key2269, 2), (key2000, 2), (key2269, 2)]

def rawRow2625 : Integer.Sparse Key := [(key2340, -2), (key2269, -2), (key2269, -2), (key2267, 6), (key2349, 2), (key2292, 2), (key2292, 2), (key2267, -2), (key2267, -2), (key1998, -2), (key2292, -6), (key2269, 2), (key2269, 2), (key2000, 2)]

def rawRow2627 : Integer.Sparse Key := [(key2292, -2), (key2292, -2), (key2349, -2), (key2292, 6), (key2269, 2), (key2269, 2), (key2340, 2), (key2000, -2), (key2269, -2), (key2269, -2), (key2267, -6), (key1998, 2), (key2267, 2), (key2267, 2)]

def rawRow2628 : Integer.Sparse Key := [(key2292, -2), (key2349, -2), (key2292, -2), (key2292, 6), (key2269, 2), (key2340, 2), (key2269, 2), (key2269, -2), (key2000, -2), (key2269, -2), (key2267, -6), (key2267, 2), (key1998, 2), (key2267, 2)]

def rawRow2629 : Integer.Sparse Key := [(key2349, -2), (key2292, -2), (key2292, -2), (key2292, 6), (key2340, 2), (key2269, 2), (key2269, 2), (key2269, -2), (key2269, -2), (key2000, -2), (key2267, -6), (key2267, 2), (key2267, 2), (key1998, 2)]

def rawRow2630 : Integer.Sparse Key := [(key2006, -2), (key2007, -2), (key2007, -2), (key2007, 6), (key2299, 2), (key2300, 2), (key2300, 2), (key2300, -2), (key2300, -2), (key2313, -2), (key2340, -6), (key2340, 2), (key2340, 2), (key2349, 2)]

def rawRow2631 : Integer.Sparse Key := [(key2007, -2), (key2006, -2), (key2007, -2), (key2007, 6), (key2300, 2), (key2299, 2), (key2300, 2), (key2300, -2), (key2313, -2), (key2300, -2), (key2340, -6), (key2340, 2), (key2349, 2), (key2340, 2)]

def rawRow2632 : Integer.Sparse Key := [(key2007, -2), (key2007, -2), (key2006, -2), (key2007, 6), (key2300, 2), (key2300, 2), (key2299, 2), (key2313, -2), (key2300, -2), (key2300, -2), (key2340, -6), (key2349, 2), (key2340, 2), (key2340, 2)]

def rawRow2634 : Integer.Sparse Key := [(key2299, -2), (key2300, -2), (key2300, -2), (key2340, 6), (key2006, 2), (key2007, 2), (key2007, 2), (key2340, -2), (key2340, -2), (key2349, -2), (key2007, -6), (key2300, 2), (key2300, 2), (key2313, 2)]

def rawRow2635 : Integer.Sparse Key := [(key2300, -2), (key2299, -2), (key2300, -2), (key2340, 6), (key2007, 2), (key2006, 2), (key2007, 2), (key2340, -2), (key2349, -2), (key2340, -2), (key2007, -6), (key2300, 2), (key2313, 2), (key2300, 2)]

def rawRow2636 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2299, -2), (key2340, 6), (key2007, 2), (key2007, 2), (key2006, 2), (key2349, -2), (key2340, -2), (key2340, -2), (key2007, -6), (key2313, 2), (key2300, 2), (key2300, 2)]

def rawRow2637 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2340, -2), (key2299, 6), (key2313, 2), (key2313, 2), (key2349, 2), (key2006, -2), (key2299, -2), (key2299, -2), (key2313, -6), (key2007, 2), (key2300, 2), (key2300, 2)]

def rawRow2638 : Integer.Sparse Key := [(key2300, -2), (key2340, -2), (key2300, -2), (key2299, 6), (key2313, 2), (key2349, 2), (key2313, 2), (key2299, -2), (key2006, -2), (key2299, -2), (key2313, -6), (key2300, 2), (key2007, 2), (key2300, 2)]

def rawRow2639 : Integer.Sparse Key := [(key2340, -2), (key2300, -2), (key2300, -2), (key2299, 6), (key2349, 2), (key2313, 2), (key2313, 2), (key2299, -2), (key2299, -2), (key2006, -2), (key2313, -6), (key2300, 2), (key2300, 2), (key2007, 2)]

def rawRow2641 : Integer.Sparse Key := [(key2313, -2), (key2313, -2), (key2349, -2), (key2313, 6), (key2300, 2), (key2300, 2), (key2340, 2), (key2007, -2), (key2300, -2), (key2300, -2), (key2299, -6), (key2006, 2), (key2299, 2), (key2299, 2)]

def rawRow2642 : Integer.Sparse Key := [(key2313, -2), (key2349, -2), (key2313, -2), (key2313, 6), (key2300, 2), (key2340, 2), (key2300, 2), (key2300, -2), (key2007, -2), (key2300, -2), (key2299, -6), (key2299, 2), (key2006, 2), (key2299, 2)]

def rawRow2643 : Integer.Sparse Key := [(key2349, -2), (key2313, -2), (key2313, -2), (key2313, 6), (key2340, 2), (key2300, 2), (key2300, 2), (key2300, -2), (key2300, -2), (key2007, -2), (key2299, -6), (key2299, 2), (key2299, 2), (key2006, 2)]

def rawRow2644 : Integer.Sparse Key := [(key2091, -2), (key2092, -2), (key2092, -2), (key2091, 1), (key2092, 1), (key2091, 1), (key2095, 1), (key2092, 1), (key2095, 1), (key2193, 2), (key2194, 2), (key2194, 2), (key2193, -1), (key2194, -1), (key2193, -1), (key2200, -1), (key2194, -1), (key2200, -1), (key2302, -1), (key2303, -1), (key2302, -1), (key2305, -1), (key2303, -1), (key2305, -1), (key2302, 1), (key2303, 1), (key2302, 1), (key2310, 1), (key2303, 1), (key2310, 1)]

def rawRow2645 : Integer.Sparse Key := [(key2092, -2), (key2091, -2), (key2092, -2), (key2092, 1), (key2091, 1), (key2095, 1), (key2091, 1), (key2095, 1), (key2092, 1), (key2194, 2), (key2193, 2), (key2194, 2), (key2194, -1), (key2193, -1), (key2200, -1), (key2193, -1), (key2200, -1), (key2194, -1), (key2303, -1), (key2302, -1), (key2305, -1), (key2302, -1), (key2305, -1), (key2303, -1), (key2303, 1), (key2302, 1), (key2310, 1), (key2302, 1), (key2310, 1), (key2303, 1)]

def rawRow2646 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2091, -2), (key2095, 1), (key2095, 1), (key2092, 1), (key2092, 1), (key2091, 1), (key2091, 1), (key2194, 2), (key2194, 2), (key2193, 2), (key2200, -1), (key2200, -1), (key2194, -1), (key2194, -1), (key2193, -1), (key2193, -1), (key2305, -1), (key2305, -1), (key2303, -1), (key2303, -1), (key2302, -1), (key2302, -1), (key2310, 1), (key2310, 1), (key2303, 1), (key2303, 1), (key2302, 1), (key2302, 1)]

def rawRow2648 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2194, -2), (key2302, 1), (key2303, 1), (key2302, 1), (key2305, 1), (key2303, 1), (key2305, 1), (key2091, 2), (key2092, 2), (key2092, 2), (key2302, -1), (key2303, -1), (key2302, -1), (key2310, -1), (key2303, -1), (key2310, -1), (key2091, -1), (key2092, -1), (key2091, -1), (key2095, -1), (key2092, -1), (key2095, -1), (key2193, 1), (key2194, 1), (key2193, 1), (key2200, 1), (key2194, 1), (key2200, 1)]

def rawRow2649 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2194, -2), (key2303, 1), (key2302, 1), (key2305, 1), (key2302, 1), (key2305, 1), (key2303, 1), (key2092, 2), (key2091, 2), (key2092, 2), (key2303, -1), (key2302, -1), (key2310, -1), (key2302, -1), (key2310, -1), (key2303, -1), (key2092, -1), (key2091, -1), (key2095, -1), (key2091, -1), (key2095, -1), (key2092, -1), (key2194, 1), (key2193, 1), (key2200, 1), (key2193, 1), (key2200, 1), (key2194, 1)]

def rawRow2650 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2193, -2), (key2305, 1), (key2305, 1), (key2303, 1), (key2303, 1), (key2302, 1), (key2302, 1), (key2092, 2), (key2092, 2), (key2091, 2), (key2310, -1), (key2310, -1), (key2303, -1), (key2303, -1), (key2302, -1), (key2302, -1), (key2095, -1), (key2095, -1), (key2092, -1), (key2092, -1), (key2091, -1), (key2091, -1), (key2200, 1), (key2200, 1), (key2194, 1), (key2194, 1), (key2193, 1), (key2193, 1)]

def rawRow2651 : Integer.Sparse Key := [(key2305, -2), (key2305, -2), (key2343, -2), (key2194, 1), (key2194, 1), (key2303, 1), (key2303, 1), (key2341, 1), (key2341, 1), (key2310, 2), (key2310, 2), (key2347, 2), (key2092, -1), (key2092, -1), (key2303, -1), (key2303, -1), (key2341, -1), (key2341, -1), (key2200, -1), (key2200, -1), (key2310, -1), (key2310, -1), (key2347, -1), (key2347, -1), (key2095, 1), (key2095, 1), (key2305, 1), (key2305, 1), (key2343, 1), (key2343, 1)]

def rawRow2652 : Integer.Sparse Key := [(key2305, -2), (key2343, -2), (key2305, -2), (key2303, 1), (key2341, 1), (key2194, 1), (key2341, 1), (key2194, 1), (key2303, 1), (key2310, 2), (key2347, 2), (key2310, 2), (key2303, -1), (key2341, -1), (key2092, -1), (key2341, -1), (key2092, -1), (key2303, -1), (key2310, -1), (key2347, -1), (key2200, -1), (key2347, -1), (key2200, -1), (key2310, -1), (key2305, 1), (key2343, 1), (key2095, 1), (key2343, 1), (key2095, 1), (key2305, 1)]

def rawRow2653 : Integer.Sparse Key := [(key2343, -2), (key2305, -2), (key2305, -2), (key2341, 1), (key2303, 1), (key2341, 1), (key2194, 1), (key2303, 1), (key2194, 1), (key2347, 2), (key2310, 2), (key2310, 2), (key2341, -1), (key2303, -1), (key2341, -1), (key2092, -1), (key2303, -1), (key2092, -1), (key2347, -1), (key2310, -1), (key2347, -1), (key2200, -1), (key2310, -1), (key2200, -1), (key2343, 1), (key2305, 1), (key2343, 1), (key2095, 1), (key2305, 1), (key2095, 1)]

def rawRow2655 : Integer.Sparse Key := [(key2310, -2), (key2310, -2), (key2347, -2), (key2200, 1), (key2200, 1), (key2310, 1), (key2310, 1), (key2347, 1), (key2347, 1), (key2305, 2), (key2305, 2), (key2343, 2), (key2095, -1), (key2095, -1), (key2305, -1), (key2305, -1), (key2343, -1), (key2343, -1), (key2194, -1), (key2194, -1), (key2303, -1), (key2303, -1), (key2341, -1), (key2341, -1), (key2092, 1), (key2092, 1), (key2303, 1), (key2303, 1), (key2341, 1), (key2341, 1)]

def rawRow2656 : Integer.Sparse Key := [(key2310, -2), (key2347, -2), (key2310, -2), (key2310, 1), (key2347, 1), (key2200, 1), (key2347, 1), (key2200, 1), (key2310, 1), (key2305, 2), (key2343, 2), (key2305, 2), (key2305, -1), (key2343, -1), (key2095, -1), (key2343, -1), (key2095, -1), (key2305, -1), (key2303, -1), (key2341, -1), (key2194, -1), (key2341, -1), (key2194, -1), (key2303, -1), (key2303, 1), (key2341, 1), (key2092, 1), (key2341, 1), (key2092, 1), (key2303, 1)]

def rawRow2657 : Integer.Sparse Key := [(key2347, -2), (key2310, -2), (key2310, -2), (key2347, 1), (key2310, 1), (key2347, 1), (key2200, 1), (key2310, 1), (key2200, 1), (key2343, 2), (key2305, 2), (key2305, 2), (key2343, -1), (key2305, -1), (key2343, -1), (key2095, -1), (key2305, -1), (key2095, -1), (key2341, -1), (key2303, -1), (key2341, -1), (key2194, -1), (key2303, -1), (key2194, -1), (key2341, 1), (key2303, 1), (key2341, 1), (key2092, 1), (key2303, 1), (key2092, 1)]

def rawRow2658 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key778, -2), (key778, 6), (key801, 2), (key803, 2), (key803, 2), (key803, -2), (key803, -2), (key811, -2), (key836, -6), (key836, 2), (key836, 2), (key839, 2)]

def rawRow2659 : Integer.Sparse Key := [(key778, -2), (key776, -2), (key778, -2), (key778, 6), (key803, 2), (key801, 2), (key803, 2), (key803, -2), (key811, -2), (key803, -2), (key836, -6), (key836, 2), (key839, 2), (key836, 2)]

def rawRow2660 : Integer.Sparse Key := [(key778, -2), (key778, -2), (key776, -2), (key778, 6), (key803, 2), (key803, 2), (key801, 2), (key811, -2), (key803, -2), (key803, -2), (key836, -6), (key839, 2), (key836, 2), (key836, 2)]

def rawRow2662 : Integer.Sparse Key := [(key801, -2), (key803, -2), (key803, -2), (key811, 6), (key776, 2), (key778, 2), (key778, 2), (key836, -2), (key836, -2), (key839, -2), (key778, -6), (key803, 2), (key803, 2), (key811, 2)]

def rawRow2663 : Integer.Sparse Key := [(key803, -2), (key801, -2), (key803, -2), (key811, 6), (key778, 2), (key776, 2), (key778, 2), (key836, -2), (key839, -2), (key836, -2), (key778, -6), (key803, 2), (key811, 2), (key803, 2)]

def rawRow2664 : Integer.Sparse Key := [(key803, -2), (key803, -2), (key801, -2), (key811, 6), (key778, 2), (key778, 2), (key776, 2), (key839, -2), (key836, -2), (key836, -2), (key778, -6), (key811, 2), (key803, 2), (key803, 2)]

def rawRow2665 : Integer.Sparse Key := [(key803, -2), (key803, -2), (key811, -2), (key801, 6), (key836, 2), (key836, 2), (key839, 2), (key776, -2), (key801, -2), (key801, -2), (key811, -6), (key778, 2), (key803, 2), (key803, 2)]

def rawRow2666 : Integer.Sparse Key := [(key803, -2), (key811, -2), (key803, -2), (key801, 6), (key836, 2), (key839, 2), (key836, 2), (key801, -2), (key776, -2), (key801, -2), (key811, -6), (key803, 2), (key778, 2), (key803, 2)]

def rawRow2667 : Integer.Sparse Key := [(key811, -2), (key803, -2), (key803, -2), (key801, 6), (key839, 2), (key836, 2), (key836, 2), (key801, -2), (key801, -2), (key776, -2), (key811, -6), (key803, 2), (key803, 2), (key778, 2)]

def rawRow2669 : Integer.Sparse Key := [(key836, -2), (key836, -2), (key839, -2), (key836, 6), (key803, 2), (key803, 2), (key811, 2), (key778, -2), (key803, -2), (key803, -2), (key801, -6), (key776, 2), (key801, 2), (key801, 2)]

def rawRow2670 : Integer.Sparse Key := [(key836, -2), (key839, -2), (key836, -2), (key836, 6), (key803, 2), (key811, 2), (key803, 2), (key803, -2), (key778, -2), (key803, -2), (key801, -6), (key801, 2), (key776, 2), (key801, 2)]

def rawRow2671 : Integer.Sparse Key := [(key839, -2), (key836, -2), (key836, -2), (key836, 6), (key811, 2), (key803, 2), (key803, 2), (key803, -2), (key803, -2), (key778, -2), (key801, -6), (key801, 2), (key801, 2), (key776, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2696 : Integer.Sparse Key := [(key1254, -6), (key1254, 2), (key1263, 2), (key1263, 2), (key1529, 6), (key1529, -2), (key1763, -2), (key1763, -2), (key1607, -2), (key1646, -2), (key1646, -2), (key1607, 2), (key1804, 2), (key1804, 2)]

def rawRow2697 : Integer.Sparse Key := [(key1254, -6), (key1263, 2), (key1254, 2), (key1263, 2), (key1529, 6), (key1763, -2), (key1529, -2), (key1763, -2), (key1646, -2), (key1607, -2), (key1646, -2), (key1804, 2), (key1607, 2), (key1804, 2)]

def rawRow2698 : Integer.Sparse Key := [(key1254, -6), (key1263, 2), (key1263, 2), (key1254, 2), (key1529, 6), (key1763, -2), (key1763, -2), (key1529, -2), (key1646, -2), (key1646, -2), (key1607, -2), (key1804, 2), (key1804, 2), (key1607, 2)]

def rawRow2699 : Integer.Sparse Key := [(key1263, -6), (key1254, 2), (key1254, 2), (key1263, 2), (key1763, 6), (key1529, -2), (key1529, -2), (key1763, -2), (key1804, -2), (key1804, -2), (key1835, -2), (key1646, 2), (key1646, 2), (key1835, 2)]

def rawRow2700 : Integer.Sparse Key := [(key1263, -6), (key1254, 2), (key1263, 2), (key1254, 2), (key1763, 6), (key1529, -2), (key1763, -2), (key1529, -2), (key1804, -2), (key1835, -2), (key1804, -2), (key1646, 2), (key1835, 2), (key1646, 2)]

def rawRow2701 : Integer.Sparse Key := [(key1263, -6), (key1263, 2), (key1254, 2), (key1254, 2), (key1763, 6), (key1763, -2), (key1529, -2), (key1529, -2), (key1835, -2), (key1804, -2), (key1804, -2), (key1835, 2), (key1646, 2), (key1646, 2)]

def rawRow2702 : Integer.Sparse Key := [(key1529, -6), (key1607, 2), (key1646, 2), (key1646, 2), (key1254, 6), (key1607, -2), (key1804, -2), (key1804, -2), (key1254, -2), (key1263, -2), (key1263, -2), (key1529, 2), (key1763, 2), (key1763, 2)]

def rawRow2703 : Integer.Sparse Key := [(key1529, -6), (key1646, 2), (key1607, 2), (key1646, 2), (key1254, 6), (key1804, -2), (key1607, -2), (key1804, -2), (key1263, -2), (key1254, -2), (key1263, -2), (key1763, 2), (key1529, 2), (key1763, 2)]

def rawRow2704 : Integer.Sparse Key := [(key1529, -6), (key1646, 2), (key1646, 2), (key1607, 2), (key1254, 6), (key1804, -2), (key1804, -2), (key1607, -2), (key1263, -2), (key1263, -2), (key1254, -2), (key1763, 2), (key1763, 2), (key1529, 2)]

def rawRow2705 : Integer.Sparse Key := [(key1646, -6), (key1529, 2), (key1607, 2), (key1646, 2), (key1804, 6), (key1254, -2), (key1607, -2), (key1804, -2), (key1763, -2), (key1804, -2), (key1835, -2), (key1263, 2), (key1646, 2), (key1835, 2)]

def rawRow2706 : Integer.Sparse Key := [(key1646, -6), (key1529, 2), (key1646, 2), (key1607, 2), (key1804, 6), (key1254, -2), (key1804, -2), (key1607, -2), (key1763, -2), (key1835, -2), (key1804, -2), (key1263, 2), (key1835, 2), (key1646, 2)]

def rawRow2707 : Integer.Sparse Key := [(key1646, -6), (key1607, 2), (key1529, 2), (key1646, 2), (key1804, 6), (key1607, -2), (key1254, -2), (key1804, -2), (key1804, -2), (key1763, -2), (key1835, -2), (key1646, 2), (key1263, 2), (key1835, 2)]

def rawRow2708 : Integer.Sparse Key := [(key1646, -6), (key1607, 2), (key1646, 2), (key1529, 2), (key1804, 6), (key1607, -2), (key1804, -2), (key1254, -2), (key1804, -2), (key1835, -2), (key1763, -2), (key1646, 2), (key1835, 2), (key1263, 2)]

def rawRow2709 : Integer.Sparse Key := [(key1646, -6), (key1646, 2), (key1529, 2), (key1607, 2), (key1804, 6), (key1804, -2), (key1254, -2), (key1607, -2), (key1835, -2), (key1763, -2), (key1804, -2), (key1835, 2), (key1263, 2), (key1646, 2)]

def rawRow2710 : Integer.Sparse Key := [(key1646, -6), (key1646, 2), (key1607, 2), (key1529, 2), (key1804, 6), (key1804, -2), (key1607, -2), (key1254, -2), (key1835, -2), (key1804, -2), (key1763, -2), (key1835, 2), (key1646, 2), (key1263, 2)]

def rawRow2711 : Integer.Sparse Key := [(key1763, -6), (key1804, 2), (key1804, 2), (key1835, 2), (key1263, 6), (key1646, -2), (key1646, -2), (key1835, -2), (key1254, -2), (key1254, -2), (key1263, -2), (key1529, 2), (key1529, 2), (key1763, 2)]

def rawRow2712 : Integer.Sparse Key := [(key1763, -6), (key1804, 2), (key1835, 2), (key1804, 2), (key1263, 6), (key1646, -2), (key1835, -2), (key1646, -2), (key1254, -2), (key1263, -2), (key1254, -2), (key1529, 2), (key1763, 2), (key1529, 2)]

def rawRow2713 : Integer.Sparse Key := [(key1763, -6), (key1835, 2), (key1804, 2), (key1804, 2), (key1263, 6), (key1835, -2), (key1646, -2), (key1646, -2), (key1263, -2), (key1254, -2), (key1254, -2), (key1763, 2), (key1529, 2), (key1529, 2)]

def rawRow2714 : Integer.Sparse Key := [(key1804, -6), (key1763, 2), (key1804, 2), (key1835, 2), (key1646, 6), (key1263, -2), (key1646, -2), (key1835, -2), (key1529, -2), (key1607, -2), (key1646, -2), (key1254, 2), (key1607, 2), (key1804, 2)]

def rawRow2715 : Integer.Sparse Key := [(key1804, -6), (key1763, 2), (key1835, 2), (key1804, 2), (key1646, 6), (key1263, -2), (key1835, -2), (key1646, -2), (key1529, -2), (key1646, -2), (key1607, -2), (key1254, 2), (key1804, 2), (key1607, 2)]

def rawRow2716 : Integer.Sparse Key := [(key1804, -6), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 6), (key1646, -2), (key1263, -2), (key1835, -2), (key1607, -2), (key1529, -2), (key1646, -2), (key1607, 2), (key1254, 2), (key1804, 2)]

def rawRow2717 : Integer.Sparse Key := [(key1804, -6), (key1804, 2), (key1835, 2), (key1763, 2), (key1646, 6), (key1646, -2), (key1835, -2), (key1263, -2), (key1607, -2), (key1646, -2), (key1529, -2), (key1607, 2), (key1804, 2), (key1254, 2)]

def rawRow2718 : Integer.Sparse Key := [(key1804, -6), (key1835, 2), (key1763, 2), (key1804, 2), (key1646, 6), (key1835, -2), (key1263, -2), (key1646, -2), (key1646, -2), (key1529, -2), (key1607, -2), (key1804, 2), (key1254, 2), (key1607, 2)]

def rawRow2719 : Integer.Sparse Key := [(key1804, -6), (key1835, 2), (key1804, 2), (key1763, 2), (key1646, 6), (key1835, -2), (key1646, -2), (key1263, -2), (key1646, -2), (key1607, -2), (key1529, -2), (key1804, 2), (key1607, 2), (key1254, 2)]

def rawRow2744 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key984, -2), (key984, 6), (key1090, 2), (key1090, 2), (key1098, 2), (key1098, -2), (key1183, -2), (key1183, -2), (key1169, -6), (key1169, 2), (key1220, 2), (key1220, 2)]

def rawRow2745 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key976, -2), (key984, 6), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, -2), (key1098, -2), (key1183, -2), (key1169, -6), (key1220, 2), (key1169, 2), (key1220, 2)]

def rawRow2746 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key976, -2), (key984, 6), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, -2), (key1183, -2), (key1098, -2), (key1169, -6), (key1220, 2), (key1220, 2), (key1169, 2)]

def rawRow2747 : Integer.Sparse Key := [(key976, -2), (key984, -2), (key984, -2), (key976, 6), (key1180, 2), (key1183, 2), (key1183, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1220, -6), (key1169, 2), (key1169, 2), (key1220, 2)]

def rawRow2748 : Integer.Sparse Key := [(key984, -2), (key976, -2), (key984, -2), (key976, 6), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1220, -6), (key1169, 2), (key1220, 2), (key1169, 2)]

def rawRow2749 : Integer.Sparse Key := [(key984, -2), (key984, -2), (key976, -2), (key976, 6), (key1183, 2), (key1183, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1220, -6), (key1220, 2), (key1169, 2), (key1169, 2)]

def rawRow2750 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1098, -2), (key1169, 6), (key976, 2), (key976, 2), (key984, 2), (key1169, -2), (key1220, -2), (key1220, -2), (key984, -6), (key1098, 2), (key1183, 2), (key1183, 2)]

def rawRow2751 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1090, -2), (key1169, 6), (key976, 2), (key984, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1220, -2), (key984, -6), (key1183, 2), (key1098, 2), (key1183, 2)]

def rawRow2752 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1090, -2), (key1169, 6), (key984, 2), (key976, 2), (key976, 2), (key1220, -2), (key1220, -2), (key1169, -2), (key984, -6), (key1183, 2), (key1183, 2), (key1098, 2)]

def rawRow2753 : Integer.Sparse Key := [(key1090, -2), (key1098, -2), (key1169, -2), (key1090, 6), (key1180, 2), (key1183, 2), (key1220, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1183, -6), (key984, 2), (key1098, 2), (key1183, 2)]

def rawRow2754 : Integer.Sparse Key := [(key1098, -2), (key1090, -2), (key1169, -2), (key1090, 6), (key1183, 2), (key1180, 2), (key1220, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1183, -6), (key984, 2), (key1183, 2), (key1098, 2)]

def rawRow2755 : Integer.Sparse Key := [(key1090, -2), (key1169, -2), (key1098, -2), (key1090, 6), (key1180, 2), (key1220, 2), (key1183, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1183, -6), (key1098, 2), (key984, 2), (key1183, 2)]

def rawRow2756 : Integer.Sparse Key := [(key1169, -2), (key1090, -2), (key1098, -2), (key1090, 6), (key1220, 2), (key1180, 2), (key1183, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1183, -6), (key1098, 2), (key1183, 2), (key984, 2)]

def rawRow2757 : Integer.Sparse Key := [(key1098, -2), (key1169, -2), (key1090, -2), (key1090, 6), (key1183, 2), (key1220, 2), (key1180, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1183, -6), (key1183, 2), (key984, 2), (key1098, 2)]

def rawRow2758 : Integer.Sparse Key := [(key1169, -2), (key1098, -2), (key1090, -2), (key1090, 6), (key1220, 2), (key1183, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1183, -6), (key1183, 2), (key1098, 2), (key984, 2)]

def rawRow2759 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1183, -2), (key1220, 6), (key976, 2), (key984, 2), (key984, 2), (key1169, -2), (key1169, -2), (key1220, -2), (key976, -6), (key1090, 2), (key1090, 2), (key1180, 2)]

def rawRow2760 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1183, -2), (key1220, 6), (key984, 2), (key976, 2), (key984, 2), (key1169, -2), (key1220, -2), (key1169, -2), (key976, -6), (key1090, 2), (key1180, 2), (key1090, 2)]

def rawRow2761 : Integer.Sparse Key := [(key1183, -2), (key1183, -2), (key1180, -2), (key1220, 6), (key984, 2), (key984, 2), (key976, 2), (key1220, -2), (key1169, -2), (key1169, -2), (key976, -6), (key1180, 2), (key1090, 2), (key1090, 2)]

def rawRow2762 : Integer.Sparse Key := [(key1180, -2), (key1183, -2), (key1220, -2), (key1183, 6), (key1090, 2), (key1098, 2), (key1169, 2), (key984, -2), (key1098, -2), (key1183, -2), (key1090, -6), (key976, 2), (key1090, 2), (key1180, 2)]

def rawRow2763 : Integer.Sparse Key := [(key1183, -2), (key1180, -2), (key1220, -2), (key1183, 6), (key1098, 2), (key1090, 2), (key1169, 2), (key984, -2), (key1183, -2), (key1098, -2), (key1090, -6), (key976, 2), (key1180, 2), (key1090, 2)]

def rawRow2764 : Integer.Sparse Key := [(key1180, -2), (key1220, -2), (key1183, -2), (key1183, 6), (key1090, 2), (key1169, 2), (key1098, 2), (key1098, -2), (key984, -2), (key1183, -2), (key1090, -6), (key1090, 2), (key976, 2), (key1180, 2)]

def rawRow2765 : Integer.Sparse Key := [(key1220, -2), (key1180, -2), (key1183, -2), (key1183, 6), (key1169, 2), (key1090, 2), (key1098, 2), (key1098, -2), (key1183, -2), (key984, -2), (key1090, -6), (key1090, 2), (key1180, 2), (key976, 2)]

def rawRow2766 : Integer.Sparse Key := [(key1183, -2), (key1220, -2), (key1180, -2), (key1183, 6), (key1098, 2), (key1169, 2), (key1090, 2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -6), (key1180, 2), (key976, 2), (key1090, 2)]

def rawRow2767 : Integer.Sparse Key := [(key1220, -2), (key1183, -2), (key1180, -2), (key1183, 6), (key1169, 2), (key1098, 2), (key1090, 2), (key1183, -2), (key1098, -2), (key984, -2), (key1090, -6), (key1180, 2), (key1090, 2), (key976, 2)]

def rawRow2768 : Integer.Sparse Key := [(key2377, -6), (key2377, 2), (key2389, 2), (key2389, 2), (key2405, 6), (key2405, -2), (key2436, -2), (key2436, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2471, 2), (key2502, 2), (key2502, 2)]

def rawRow2769 : Integer.Sparse Key := [(key2377, -6), (key2389, 2), (key2377, 2), (key2389, 2), (key2405, 6), (key2436, -2), (key2405, -2), (key2436, -2), (key2479, -2), (key2471, -2), (key2479, -2), (key2502, 2), (key2471, 2), (key2502, 2)]

def rawRow2770 : Integer.Sparse Key := [(key2377, -6), (key2389, 2), (key2389, 2), (key2377, 2), (key2405, 6), (key2436, -2), (key2436, -2), (key2405, -2), (key2479, -2), (key2479, -2), (key2471, -2), (key2502, 2), (key2502, 2), (key2471, 2)]

def rawRow2771 : Integer.Sparse Key := [(key2389, -6), (key2377, 2), (key2377, 2), (key2389, 2), (key2436, 6), (key2405, -2), (key2405, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2479, 2), (key2479, 2), (key2518, 2)]

def rawRow2772 : Integer.Sparse Key := [(key2389, -6), (key2377, 2), (key2389, 2), (key2377, 2), (key2436, 6), (key2405, -2), (key2436, -2), (key2405, -2), (key2502, -2), (key2518, -2), (key2502, -2), (key2479, 2), (key2518, 2), (key2479, 2)]

def rawRow2773 : Integer.Sparse Key := [(key2389, -6), (key2389, 2), (key2377, 2), (key2377, 2), (key2436, 6), (key2436, -2), (key2405, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2502, -2), (key2518, 2), (key2479, 2), (key2479, 2)]

def rawRow2774 : Integer.Sparse Key := [(key2405, -6), (key2471, 2), (key2479, 2), (key2479, 2), (key2377, 6), (key2471, -2), (key2502, -2), (key2502, -2), (key2377, -2), (key2389, -2), (key2389, -2), (key2405, 2), (key2436, 2), (key2436, 2)]

def rawRow2775 : Integer.Sparse Key := [(key2405, -6), (key2479, 2), (key2471, 2), (key2479, 2), (key2377, 6), (key2502, -2), (key2471, -2), (key2502, -2), (key2389, -2), (key2377, -2), (key2389, -2), (key2436, 2), (key2405, 2), (key2436, 2)]

def rawRow2776 : Integer.Sparse Key := [(key2405, -6), (key2479, 2), (key2479, 2), (key2471, 2), (key2377, 6), (key2502, -2), (key2502, -2), (key2471, -2), (key2389, -2), (key2389, -2), (key2377, -2), (key2436, 2), (key2436, 2), (key2405, 2)]

def rawRow2777 : Integer.Sparse Key := [(key2479, -6), (key2405, 2), (key2471, 2), (key2479, 2), (key2502, 6), (key2377, -2), (key2471, -2), (key2502, -2), (key2436, -2), (key2502, -2), (key2518, -2), (key2389, 2), (key2479, 2), (key2518, 2)]

def rawRow2778 : Integer.Sparse Key := [(key2479, -6), (key2405, 2), (key2479, 2), (key2471, 2), (key2502, 6), (key2377, -2), (key2502, -2), (key2471, -2), (key2436, -2), (key2518, -2), (key2502, -2), (key2389, 2), (key2518, 2), (key2479, 2)]

def rawRow2779 : Integer.Sparse Key := [(key2479, -6), (key2471, 2), (key2405, 2), (key2479, 2), (key2502, 6), (key2471, -2), (key2377, -2), (key2502, -2), (key2502, -2), (key2436, -2), (key2518, -2), (key2479, 2), (key2389, 2), (key2518, 2)]

def rawRow2780 : Integer.Sparse Key := [(key2479, -6), (key2471, 2), (key2479, 2), (key2405, 2), (key2502, 6), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2479, 2), (key2518, 2), (key2389, 2)]

def rawRow2781 : Integer.Sparse Key := [(key2479, -6), (key2479, 2), (key2405, 2), (key2471, 2), (key2502, 6), (key2502, -2), (key2377, -2), (key2471, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2518, 2), (key2389, 2), (key2479, 2)]

def rawRow2782 : Integer.Sparse Key := [(key2479, -6), (key2479, 2), (key2471, 2), (key2405, 2), (key2502, 6), (key2502, -2), (key2471, -2), (key2377, -2), (key2518, -2), (key2502, -2), (key2436, -2), (key2518, 2), (key2479, 2), (key2389, 2)]

def rawRow2783 : Integer.Sparse Key := [(key2436, -6), (key2502, 2), (key2502, 2), (key2518, 2), (key2389, 6), (key2479, -2), (key2479, -2), (key2518, -2), (key2377, -2), (key2377, -2), (key2389, -2), (key2405, 2), (key2405, 2), (key2436, 2)]

def rawRow2784 : Integer.Sparse Key := [(key2436, -6), (key2502, 2), (key2518, 2), (key2502, 2), (key2389, 6), (key2479, -2), (key2518, -2), (key2479, -2), (key2377, -2), (key2389, -2), (key2377, -2), (key2405, 2), (key2436, 2), (key2405, 2)]

def rawRow2785 : Integer.Sparse Key := [(key2436, -6), (key2518, 2), (key2502, 2), (key2502, 2), (key2389, 6), (key2518, -2), (key2479, -2), (key2479, -2), (key2389, -2), (key2377, -2), (key2377, -2), (key2436, 2), (key2405, 2), (key2405, 2)]

def rawRow2786 : Integer.Sparse Key := [(key2502, -6), (key2436, 2), (key2502, 2), (key2518, 2), (key2479, 6), (key2389, -2), (key2479, -2), (key2518, -2), (key2405, -2), (key2471, -2), (key2479, -2), (key2377, 2), (key2471, 2), (key2502, 2)]

def rawRow2787 : Integer.Sparse Key := [(key2502, -6), (key2436, 2), (key2518, 2), (key2502, 2), (key2479, 6), (key2389, -2), (key2518, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2471, -2), (key2377, 2), (key2502, 2), (key2471, 2)]

def rawRow2788 : Integer.Sparse Key := [(key2502, -6), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 6), (key2479, -2), (key2389, -2), (key2518, -2), (key2471, -2), (key2405, -2), (key2479, -2), (key2471, 2), (key2377, 2), (key2502, 2)]

def rawRow2789 : Integer.Sparse Key := [(key2502, -6), (key2502, 2), (key2518, 2), (key2436, 2), (key2479, 6), (key2479, -2), (key2518, -2), (key2389, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, 2), (key2502, 2), (key2377, 2)]

def rawRow2790 : Integer.Sparse Key := [(key2502, -6), (key2518, 2), (key2436, 2), (key2502, 2), (key2479, 6), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, 2), (key2377, 2), (key2471, 2)]

def rawRow2791 : Integer.Sparse Key := [(key2502, -6), (key2518, 2), (key2502, 2), (key2436, 2), (key2479, 6), (key2518, -2), (key2479, -2), (key2389, -2), (key2479, -2), (key2471, -2), (key2405, -2), (key2502, 2), (key2471, 2), (key2377, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2819 : Integer.Sparse Key := [(key2421, -2), (key2430, -2), (key2430, -2), (key2421, 2), (key2428, 2), (key2428, 2), (key2496, 2), (key2510, 2), (key2510, 2), (key2496, -6), (key2574, -2), (key2577, -2), (key2577, -2), (key2574, 6)]

def rawRow2820 : Integer.Sparse Key := [(key2430, -2), (key2421, -2), (key2430, -2), (key2428, 2), (key2421, 2), (key2428, 2), (key2510, 2), (key2496, 2), (key2510, 2), (key2496, -6), (key2577, -2), (key2574, -2), (key2577, -2), (key2574, 6)]

def rawRow2821 : Integer.Sparse Key := [(key2430, -2), (key2430, -2), (key2421, -2), (key2428, 2), (key2428, 2), (key2421, 2), (key2510, 2), (key2510, 2), (key2496, 2), (key2496, -6), (key2577, -2), (key2577, -2), (key2574, -2), (key2574, 6)]

def rawRow2825 : Integer.Sparse Key := [(key3036, -2), (key3042, -2), (key3140, -2), (key3036, 2), (key3040, 2), (key3132, 2), (key3040, 2), (key3044, 2), (key3148, 2), (key2428, -6), (key2430, -2), (key2444, -2), (key2510, -2), (key2430, 6)]

def rawRow2826 : Integer.Sparse Key := [(key3042, -2), (key3036, -2), (key3140, -2), (key3040, 2), (key3036, 2), (key3132, 2), (key3044, 2), (key3040, 2), (key3148, 2), (key2428, -6), (key2444, -2), (key2430, -2), (key2510, -2), (key2430, 6)]

def rawRow2827 : Integer.Sparse Key := [(key3036, -2), (key3140, -2), (key3042, -2), (key3036, 2), (key3132, 2), (key3040, 2), (key3040, 2), (key3148, 2), (key3044, 2), (key2428, -6), (key2430, -2), (key2510, -2), (key2444, -2), (key2430, 6)]

def rawRow2828 : Integer.Sparse Key := [(key3140, -2), (key3036, -2), (key3042, -2), (key3132, 2), (key3036, 2), (key3040, 2), (key3148, 2), (key3040, 2), (key3044, 2), (key2428, -6), (key2510, -2), (key2430, -2), (key2444, -2), (key2430, 6)]

def rawRow2829 : Integer.Sparse Key := [(key3042, -2), (key3140, -2), (key3036, -2), (key3040, 2), (key3132, 2), (key3036, 2), (key3044, 2), (key3148, 2), (key3040, 2), (key2428, -6), (key2444, -2), (key2510, -2), (key2430, -2), (key2430, 6)]

def rawRow2830 : Integer.Sparse Key := [(key3140, -2), (key3042, -2), (key3036, -2), (key3132, 2), (key3040, 2), (key3036, 2), (key3148, 2), (key3044, 2), (key3040, 2), (key2428, -6), (key2510, -2), (key2444, -2), (key2430, -2), (key2430, 6)]

def rawRow2831 : Integer.Sparse Key := [(key3132, -2), (key3145, -2), (key3145, -2), (key3140, 2), (key3148, 2), (key3148, 2), (key3036, 2), (key3042, 2), (key3042, 2), (key3140, -6), (key2421, -2), (key2428, -2), (key2428, -2), (key2496, 6)]

def rawRow2832 : Integer.Sparse Key := [(key3145, -2), (key3132, -2), (key3145, -2), (key3148, 2), (key3140, 2), (key3148, 2), (key3042, 2), (key3036, 2), (key3042, 2), (key3140, -6), (key2428, -2), (key2421, -2), (key2428, -2), (key2496, 6)]

def rawRow2833 : Integer.Sparse Key := [(key3145, -2), (key3145, -2), (key3132, -2), (key3148, 2), (key3148, 2), (key3140, 2), (key3042, 2), (key3042, 2), (key3036, 2), (key3140, -6), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, 6)]

def rawRow2834 : Integer.Sparse Key := [(key3040, -2), (key3044, -2), (key3148, -2), (key3042, 2), (key3044, 2), (key3145, 2), (key3036, 2), (key3042, 2), (key3140, 2), (key3042, -6), (key2421, -2), (key2428, -2), (key2496, -2), (key2428, 6)]

def rawRow2835 : Integer.Sparse Key := [(key3044, -2), (key3040, -2), (key3148, -2), (key3044, 2), (key3042, 2), (key3145, 2), (key3042, 2), (key3036, 2), (key3140, 2), (key3042, -6), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, 6)]

def rawRow2836 : Integer.Sparse Key := [(key3040, -2), (key3148, -2), (key3044, -2), (key3042, 2), (key3145, 2), (key3044, 2), (key3036, 2), (key3140, 2), (key3042, 2), (key3042, -6), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, 6)]

def rawRow2837 : Integer.Sparse Key := [(key3148, -2), (key3040, -2), (key3044, -2), (key3145, 2), (key3042, 2), (key3044, 2), (key3140, 2), (key3036, 2), (key3042, 2), (key3042, -6), (key2496, -2), (key2421, -2), (key2428, -2), (key2428, 6)]

def rawRow2838 : Integer.Sparse Key := [(key3044, -2), (key3148, -2), (key3040, -2), (key3044, 2), (key3145, 2), (key3042, 2), (key3042, 2), (key3140, 2), (key3036, 2), (key3042, -6), (key2428, -2), (key2496, -2), (key2421, -2), (key2428, 6)]

def rawRow2839 : Integer.Sparse Key := [(key3148, -2), (key3044, -2), (key3040, -2), (key3145, 2), (key3044, 2), (key3042, 2), (key3140, 2), (key3042, 2), (key3036, 2), (key3042, -6), (key2496, -2), (key2428, -2), (key2421, -2), (key2428, 6)]

def rawRow2864 : Integer.Sparse Key := [(key976, -2), (key976, -2), (key983, -2), (key983, 6), (key1090, 2), (key1090, 2), (key1097, 2), (key1097, -2), (key1182, -2), (key1182, -2), (key1168, -6), (key1168, 2), (key1219, 2), (key1219, 2)]

def rawRow2865 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key976, -2), (key983, 6), (key1090, 2), (key1097, 2), (key1090, 2), (key1182, -2), (key1097, -2), (key1182, -2), (key1168, -6), (key1219, 2), (key1168, 2), (key1219, 2)]

def rawRow2866 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key976, -2), (key983, 6), (key1097, 2), (key1090, 2), (key1090, 2), (key1182, -2), (key1182, -2), (key1097, -2), (key1168, -6), (key1219, 2), (key1219, 2), (key1168, 2)]

def rawRow2867 : Integer.Sparse Key := [(key976, -2), (key983, -2), (key983, -2), (key976, 6), (key1180, 2), (key1182, 2), (key1182, 2), (key1090, -2), (key1090, -2), (key1180, -2), (key1219, -6), (key1168, 2), (key1168, 2), (key1219, 2)]

def rawRow2868 : Integer.Sparse Key := [(key983, -2), (key976, -2), (key983, -2), (key976, 6), (key1182, 2), (key1180, 2), (key1182, 2), (key1090, -2), (key1180, -2), (key1090, -2), (key1219, -6), (key1168, 2), (key1219, 2), (key1168, 2)]

def rawRow2869 : Integer.Sparse Key := [(key983, -2), (key983, -2), (key976, -2), (key976, 6), (key1182, 2), (key1182, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key1090, -2), (key1219, -6), (key1219, 2), (key1168, 2), (key1168, 2)]

def rawRow2870 : Integer.Sparse Key := [(key1090, -2), (key1090, -2), (key1097, -2), (key1168, 6), (key976, 2), (key976, 2), (key983, 2), (key1168, -2), (key1219, -2), (key1219, -2), (key983, -6), (key1097, 2), (key1182, 2), (key1182, 2)]

def rawRow2871 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1090, -2), (key1168, 6), (key976, 2), (key983, 2), (key976, 2), (key1219, -2), (key1168, -2), (key1219, -2), (key983, -6), (key1182, 2), (key1097, 2), (key1182, 2)]

def rawRow2872 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1090, -2), (key1168, 6), (key983, 2), (key976, 2), (key976, 2), (key1219, -2), (key1219, -2), (key1168, -2), (key983, -6), (key1182, 2), (key1182, 2), (key1097, 2)]

def rawRow2873 : Integer.Sparse Key := [(key1090, -2), (key1097, -2), (key1168, -2), (key1090, 6), (key1180, 2), (key1182, 2), (key1219, 2), (key976, -2), (key1090, -2), (key1180, -2), (key1182, -6), (key983, 2), (key1097, 2), (key1182, 2)]

def rawRow2874 : Integer.Sparse Key := [(key1097, -2), (key1090, -2), (key1168, -2), (key1090, 6), (key1182, 2), (key1180, 2), (key1219, 2), (key976, -2), (key1180, -2), (key1090, -2), (key1182, -6), (key983, 2), (key1182, 2), (key1097, 2)]

def rawRow2875 : Integer.Sparse Key := [(key1090, -2), (key1168, -2), (key1097, -2), (key1090, 6), (key1180, 2), (key1219, 2), (key1182, 2), (key1090, -2), (key976, -2), (key1180, -2), (key1182, -6), (key1097, 2), (key983, 2), (key1182, 2)]

def rawRow2876 : Integer.Sparse Key := [(key1168, -2), (key1090, -2), (key1097, -2), (key1090, 6), (key1219, 2), (key1180, 2), (key1182, 2), (key1090, -2), (key1180, -2), (key976, -2), (key1182, -6), (key1097, 2), (key1182, 2), (key983, 2)]

def rawRow2877 : Integer.Sparse Key := [(key1097, -2), (key1168, -2), (key1090, -2), (key1090, 6), (key1182, 2), (key1219, 2), (key1180, 2), (key1180, -2), (key976, -2), (key1090, -2), (key1182, -6), (key1182, 2), (key983, 2), (key1097, 2)]

def rawRow2878 : Integer.Sparse Key := [(key1168, -2), (key1097, -2), (key1090, -2), (key1090, 6), (key1219, 2), (key1182, 2), (key1180, 2), (key1180, -2), (key1090, -2), (key976, -2), (key1182, -6), (key1182, 2), (key1097, 2), (key983, 2)]

def rawRow2879 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1182, -2), (key1219, 6), (key976, 2), (key983, 2), (key983, 2), (key1168, -2), (key1168, -2), (key1219, -2), (key976, -6), (key1090, 2), (key1090, 2), (key1180, 2)]

def rawRow2880 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1182, -2), (key1219, 6), (key983, 2), (key976, 2), (key983, 2), (key1168, -2), (key1219, -2), (key1168, -2), (key976, -6), (key1090, 2), (key1180, 2), (key1090, 2)]

def rawRow2881 : Integer.Sparse Key := [(key1182, -2), (key1182, -2), (key1180, -2), (key1219, 6), (key983, 2), (key983, 2), (key976, 2), (key1219, -2), (key1168, -2), (key1168, -2), (key976, -6), (key1180, 2), (key1090, 2), (key1090, 2)]

def rawRow2882 : Integer.Sparse Key := [(key1180, -2), (key1182, -2), (key1219, -2), (key1182, 6), (key1090, 2), (key1097, 2), (key1168, 2), (key983, -2), (key1097, -2), (key1182, -2), (key1090, -6), (key976, 2), (key1090, 2), (key1180, 2)]

def rawRow2883 : Integer.Sparse Key := [(key1182, -2), (key1180, -2), (key1219, -2), (key1182, 6), (key1097, 2), (key1090, 2), (key1168, 2), (key983, -2), (key1182, -2), (key1097, -2), (key1090, -6), (key976, 2), (key1180, 2), (key1090, 2)]

def rawRow2884 : Integer.Sparse Key := [(key1180, -2), (key1219, -2), (key1182, -2), (key1182, 6), (key1090, 2), (key1168, 2), (key1097, 2), (key1097, -2), (key983, -2), (key1182, -2), (key1090, -6), (key1090, 2), (key976, 2), (key1180, 2)]

def rawRow2885 : Integer.Sparse Key := [(key1219, -2), (key1180, -2), (key1182, -2), (key1182, 6), (key1168, 2), (key1090, 2), (key1097, 2), (key1097, -2), (key1182, -2), (key983, -2), (key1090, -6), (key1090, 2), (key1180, 2), (key976, 2)]

def rawRow2886 : Integer.Sparse Key := [(key1182, -2), (key1219, -2), (key1180, -2), (key1182, 6), (key1097, 2), (key1168, 2), (key1090, 2), (key1182, -2), (key983, -2), (key1097, -2), (key1090, -6), (key1180, 2), (key976, 2), (key1090, 2)]

def rawRow2887 : Integer.Sparse Key := [(key1219, -2), (key1182, -2), (key1180, -2), (key1182, 6), (key1168, 2), (key1097, 2), (key1090, 2), (key1182, -2), (key1097, -2), (key983, -2), (key1090, -6), (key1180, 2), (key1090, 2), (key976, 2)]

def rawRow2912 : Integer.Sparse Key := [(key2357, -2), (key2361, -2), (key2366, -2), (key2366, 6), (key2456, 2), (key2456, 2), (key2461, 2), (key2461, -2), (key2523, -2), (key2523, -2), (key2567, -6), (key2567, 2), (key2579, 2), (key2579, 2)]

def rawRow2913 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2361, -2), (key2366, 6), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, -2), (key2461, -2), (key2523, -2), (key2567, -6), (key2579, 2), (key2567, 2), (key2579, 2)]

def rawRow2914 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2361, -2), (key2366, 6), (key2461, 2), (key2456, 2), (key2456, 2), (key2523, -2), (key2523, -2), (key2461, -2), (key2567, -6), (key2579, 2), (key2579, 2), (key2567, 2)]

def rawRow2915 : Integer.Sparse Key := [(key2357, -2), (key2363, -2), (key2363, -2), (key2361, 6), (key2517, 2), (key2523, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2579, -6), (key2567, 2), (key2567, 2), (key2579, 2)]

def rawRow2916 : Integer.Sparse Key := [(key2363, -2), (key2357, -2), (key2363, -2), (key2361, 6), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2579, -6), (key2567, 2), (key2579, 2), (key2567, 2)]

def rawRow2917 : Integer.Sparse Key := [(key2363, -2), (key2363, -2), (key2357, -2), (key2361, 6), (key2523, 2), (key2523, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2579, -6), (key2579, 2), (key2567, 2), (key2567, 2)]

def rawRow2918 : Integer.Sparse Key := [(key2452, -2), (key2452, -2), (key2458, -2), (key2519, 6), (key2357, 2), (key2361, 2), (key2366, 2), (key2567, -2), (key2579, -2), (key2579, -2), (key2366, -6), (key2461, 2), (key2523, 2), (key2523, 2)]

def rawRow2919 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2452, -2), (key2519, 6), (key2357, 2), (key2363, 2), (key2361, 2), (key2579, -2), (key2567, -2), (key2579, -2), (key2366, -6), (key2523, 2), (key2461, 2), (key2523, 2)]

def rawRow2920 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2452, -2), (key2519, 6), (key2363, 2), (key2357, 2), (key2361, 2), (key2579, -2), (key2579, -2), (key2567, -2), (key2366, -6), (key2523, 2), (key2523, 2), (key2461, 2)]

def rawRow2921 : Integer.Sparse Key := [(key2452, -2), (key2458, -2), (key2519, -2), (key2452, 6), (key2528, 2), (key2530, 2), (key2560, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2523, -6), (key2366, 2), (key2461, 2), (key2523, 2)]

def rawRow2922 : Integer.Sparse Key := [(key2458, -2), (key2452, -2), (key2519, -2), (key2452, 6), (key2530, 2), (key2528, 2), (key2560, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2523, -6), (key2366, 2), (key2523, 2), (key2461, 2)]

def rawRow2923 : Integer.Sparse Key := [(key2452, -2), (key2519, -2), (key2458, -2), (key2452, 6), (key2528, 2), (key2560, 2), (key2530, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2523, -6), (key2461, 2), (key2366, 2), (key2523, 2)]

def rawRow2924 : Integer.Sparse Key := [(key2519, -2), (key2452, -2), (key2458, -2), (key2452, 6), (key2560, 2), (key2528, 2), (key2530, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2523, -6), (key2461, 2), (key2523, 2), (key2366, 2)]

def rawRow2925 : Integer.Sparse Key := [(key2458, -2), (key2519, -2), (key2452, -2), (key2452, 6), (key2530, 2), (key2560, 2), (key2528, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2523, -6), (key2523, 2), (key2366, 2), (key2461, 2)]

def rawRow2926 : Integer.Sparse Key := [(key2519, -2), (key2458, -2), (key2452, -2), (key2452, 6), (key2560, 2), (key2530, 2), (key2528, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2523, -6), (key2523, 2), (key2461, 2), (key2366, 2)]

def rawRow2927 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2530, -2), (key2560, 6), (key2357, 2), (key2363, 2), (key2363, 2), (key2519, -2), (key2519, -2), (key2560, -2), (key2361, -6), (key2456, 2), (key2456, 2), (key2517, 2)]

def rawRow2928 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2530, -2), (key2560, 6), (key2363, 2), (key2357, 2), (key2363, 2), (key2519, -2), (key2560, -2), (key2519, -2), (key2361, -6), (key2456, 2), (key2517, 2), (key2456, 2)]

def rawRow2929 : Integer.Sparse Key := [(key2530, -2), (key2530, -2), (key2528, -2), (key2560, 6), (key2363, 2), (key2363, 2), (key2357, 2), (key2560, -2), (key2519, -2), (key2519, -2), (key2361, -6), (key2517, 2), (key2456, 2), (key2456, 2)]

def rawRow2930 : Integer.Sparse Key := [(key2528, -2), (key2530, -2), (key2560, -2), (key2530, 6), (key2452, 2), (key2458, 2), (key2519, 2), (key2363, -2), (key2458, -2), (key2530, -2), (key2456, -6), (key2361, 2), (key2456, 2), (key2517, 2)]

def rawRow2931 : Integer.Sparse Key := [(key2530, -2), (key2528, -2), (key2560, -2), (key2530, 6), (key2458, 2), (key2452, 2), (key2519, 2), (key2363, -2), (key2530, -2), (key2458, -2), (key2456, -6), (key2361, 2), (key2517, 2), (key2456, 2)]

def rawRow2932 : Integer.Sparse Key := [(key2528, -2), (key2560, -2), (key2530, -2), (key2530, 6), (key2452, 2), (key2519, 2), (key2458, 2), (key2458, -2), (key2363, -2), (key2530, -2), (key2456, -6), (key2456, 2), (key2361, 2), (key2517, 2)]

def rawRow2933 : Integer.Sparse Key := [(key2560, -2), (key2528, -2), (key2530, -2), (key2530, 6), (key2519, 2), (key2452, 2), (key2458, 2), (key2458, -2), (key2530, -2), (key2363, -2), (key2456, -6), (key2456, 2), (key2517, 2), (key2361, 2)]

def rawRow2934 : Integer.Sparse Key := [(key2530, -2), (key2560, -2), (key2528, -2), (key2530, 6), (key2458, 2), (key2519, 2), (key2452, 2), (key2530, -2), (key2363, -2), (key2458, -2), (key2456, -6), (key2517, 2), (key2361, 2), (key2456, 2)]

def rawRow2935 : Integer.Sparse Key := [(key2560, -2), (key2530, -2), (key2528, -2), (key2530, 6), (key2519, 2), (key2458, 2), (key2452, 2), (key2530, -2), (key2458, -2), (key2363, -2), (key2456, -6), (key2517, 2), (key2456, 2), (key2361, 2)]

def rawRow2936 : Integer.Sparse Key := [(key2361, -2), (key2361, -2), (key2364, -2), (key2364, 6), (key2456, 2), (key2456, 2), (key2459, 2), (key2459, -2), (key2520, -2), (key2520, -2), (key2531, -6), (key2531, 2), (key2561, 2), (key2561, 2)]

def rawRow2937 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2361, -2), (key2364, 6), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, -2), (key2459, -2), (key2520, -2), (key2531, -6), (key2561, 2), (key2531, 2), (key2561, 2)]

def rawRow2938 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2361, -2), (key2364, 6), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2459, -2), (key2531, -6), (key2561, 2), (key2561, 2), (key2531, 2)]

def rawRow2942 : Integer.Sparse Key := [(key2456, -2), (key2456, -2), (key2459, -2), (key2531, 6), (key2361, 2), (key2361, 2), (key2364, 2), (key2531, -2), (key2561, -2), (key2561, -2), (key2364, -6), (key2459, 2), (key2520, 2), (key2520, 2)]

def rawRow2943 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2456, -2), (key2531, 6), (key2361, 2), (key2364, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2561, -2), (key2364, -6), (key2520, 2), (key2459, 2), (key2520, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2944 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2456, -2), (key2531, 6), (key2364, 2), (key2361, 2), (key2361, 2), (key2561, -2), (key2561, -2), (key2531, -2), (key2364, -6), (key2520, 2), (key2520, 2), (key2459, 2)]

def rawRow2945 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2531, -2), (key2456, 6), (key2517, 2), (key2520, 2), (key2561, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2520, -6), (key2364, 2), (key2459, 2), (key2520, 2)]

def rawRow2946 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2531, -2), (key2456, 6), (key2520, 2), (key2517, 2), (key2561, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2520, -6), (key2364, 2), (key2520, 2), (key2459, 2)]

def rawRow2947 : Integer.Sparse Key := [(key2456, -2), (key2531, -2), (key2459, -2), (key2456, 6), (key2517, 2), (key2561, 2), (key2520, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2520, -6), (key2459, 2), (key2364, 2), (key2520, 2)]

def rawRow2948 : Integer.Sparse Key := [(key2531, -2), (key2456, -2), (key2459, -2), (key2456, 6), (key2561, 2), (key2517, 2), (key2520, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2520, -6), (key2459, 2), (key2520, 2), (key2364, 2)]

def rawRow2949 : Integer.Sparse Key := [(key2459, -2), (key2531, -2), (key2456, -2), (key2456, 6), (key2520, 2), (key2561, 2), (key2517, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2520, -6), (key2520, 2), (key2364, 2), (key2459, 2)]

def rawRow2950 : Integer.Sparse Key := [(key2531, -2), (key2459, -2), (key2456, -2), (key2456, 6), (key2561, 2), (key2520, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2520, -6), (key2520, 2), (key2459, 2), (key2364, 2)]

def rawRow2954 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2561, -2), (key2520, 6), (key2456, 2), (key2459, 2), (key2531, 2), (key2364, -2), (key2459, -2), (key2520, -2), (key2456, -6), (key2361, 2), (key2456, 2), (key2517, 2)]

def rawRow2955 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2561, -2), (key2520, 6), (key2459, 2), (key2456, 2), (key2531, 2), (key2364, -2), (key2520, -2), (key2459, -2), (key2456, -6), (key2361, 2), (key2517, 2), (key2456, 2)]

def rawRow2956 : Integer.Sparse Key := [(key2517, -2), (key2561, -2), (key2520, -2), (key2520, 6), (key2456, 2), (key2531, 2), (key2459, 2), (key2459, -2), (key2364, -2), (key2520, -2), (key2456, -6), (key2456, 2), (key2361, 2), (key2517, 2)]

def rawRow2957 : Integer.Sparse Key := [(key2561, -2), (key2517, -2), (key2520, -2), (key2520, 6), (key2531, 2), (key2456, 2), (key2459, 2), (key2459, -2), (key2520, -2), (key2364, -2), (key2456, -6), (key2456, 2), (key2517, 2), (key2361, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow256 : Integer.Sparse Key := [(key254, -1), (key269, -1), (key254, 2), (key264, 1), (key274, 1), (key242, -1), (key264, -1), (key265, -2), (key244, 1), (key265, 1), (key322, 1), (key337, 1), (key322, -2), (key332, -1), (key343, -1), (key308, 1), (key332, 1), (key333, 2), (key310, -1), (key333, -1), (key446, -1), (key472, -1), (key412, 1), (key446, 1), (key454, 1), (key478, 1), (key391, -1), (key454, -1), (key423, -1), (key462, -1), (key402, 1), (key462, 1), (key598, 2), (key580, -1), (key598, -1), (key604, -2), (key570, 1), (key604, 1), (key586, 1), (key610, 1), (key575, -1), (key610, -1)]

def rawRow257 : Integer.Sparse Key := [(key269, -1), (key254, -1), (key254, 2), (key274, 1), (key264, 1), (key264, -1), (key242, -1), (key265, -2), (key265, 1), (key244, 1), (key337, 1), (key322, 1), (key322, -2), (key343, -1), (key332, -1), (key332, 1), (key308, 1), (key333, 2), (key333, -1), (key310, -1), (key472, -1), (key446, -1), (key446, 1), (key412, 1), (key478, 1), (key454, 1), (key454, -1), (key391, -1), (key462, -1), (key423, -1), (key462, 1), (key402, 1), (key598, 2), (key598, -1), (key580, -1), (key604, -2), (key604, 1), (key570, 1), (key610, 1), (key586, 1), (key610, -1), (key575, -1)]

def rawRow258 : Integer.Sparse Key := [(key264, -1), (key265, -1), (key274, 2), (key242, 1), (key244, 1), (key269, -1), (key274, -1), (key242, -2), (key254, 1), (key264, 1), (key332, 1), (key333, 1), (key343, -2), (key308, -1), (key310, -1), (key337, 1), (key343, 1), (key308, 2), (key322, -1), (key332, -1), (key422, -1), (key423, -1), (key478, 1), (key484, 1), (key401, 1), (key402, 1), (key472, -1), (key484, -1), (key391, -1), (key401, -1), (key412, 1), (key422, 1), (key586, 2), (key604, -1), (key610, -1), (key575, -2), (key598, 1), (key610, 1), (key570, 1), (key575, 1), (key580, -1), (key586, -1)]

def rawRow259 : Integer.Sparse Key := [(key265, -1), (key264, -1), (key274, 2), (key244, 1), (key242, 1), (key274, -1), (key269, -1), (key242, -2), (key264, 1), (key254, 1), (key333, 1), (key332, 1), (key343, -2), (key310, -1), (key308, -1), (key343, 1), (key337, 1), (key308, 2), (key332, -1), (key322, -1), (key423, -1), (key422, -1), (key484, 1), (key478, 1), (key402, 1), (key401, 1), (key484, -1), (key472, -1), (key401, -1), (key391, -1), (key422, 1), (key412, 1), (key586, 2), (key610, -1), (key604, -1), (key575, -2), (key610, 1), (key598, 1), (key575, 1), (key570, 1), (key586, -1), (key580, -1)]

def rawRow260 : Integer.Sparse Key := [(key264, -1), (key274, -1), (key265, 2), (key254, 1), (key269, 1), (key244, -1), (key265, -1), (key254, -2), (key242, 1), (key264, 1), (key332, 1), (key343, 1), (key333, -2), (key322, -1), (key337, -1), (key310, 1), (key333, 1), (key322, 2), (key308, -1), (key332, -1), (key454, -1), (key478, -1), (key423, 1), (key462, 1), (key446, 1), (key472, 1), (key402, -1), (key462, -1), (key412, -1), (key446, -1), (key391, 1), (key454, 1), (key604, 2), (key586, -1), (key610, -1), (key598, -2), (key575, 1), (key610, 1), (key580, 1), (key598, 1), (key570, -1), (key604, -1)]

def rawRow261 : Integer.Sparse Key := [(key274, -1), (key264, -1), (key265, 2), (key269, 1), (key254, 1), (key265, -1), (key244, -1), (key254, -2), (key264, 1), (key242, 1), (key343, 1), (key332, 1), (key333, -2), (key337, -1), (key322, -1), (key333, 1), (key310, 1), (key322, 2), (key332, -1), (key308, -1), (key478, -1), (key454, -1), (key462, 1), (key423, 1), (key472, 1), (key446, 1), (key462, -1), (key402, -1), (key446, -1), (key412, -1), (key454, 1), (key391, 1), (key604, 2), (key610, -1), (key586, -1), (key598, -2), (key610, 1), (key575, 1), (key598, 1), (key580, 1), (key604, -1), (key570, -1)]

def rawRow263 : Integer.Sparse Key := [(key308, -1), (key310, -1), (key308, 2), (key401, 1), (key402, 1), (key391, -1), (key401, -1), (key575, -2), (key570, 1), (key575, 1), (key242, 1), (key244, 1), (key242, -2), (key422, -1), (key423, -1), (key412, 1), (key422, 1), (key586, 2), (key580, -1), (key586, -1), (key264, -1), (key265, -1), (key254, 1), (key264, 1), (key332, 1), (key333, 1), (key322, -1), (key332, -1), (key604, -1), (key610, -1), (key598, 1), (key610, 1), (key274, 2), (key269, -1), (key274, -1), (key343, -2), (key337, 1), (key343, 1), (key478, 1), (key484, 1), (key472, -1), (key484, -1)]

def rawRow264 : Integer.Sparse Key := [(key310, -1), (key308, -1), (key308, 2), (key402, 1), (key401, 1), (key401, -1), (key391, -1), (key575, -2), (key575, 1), (key570, 1), (key244, 1), (key242, 1), (key242, -2), (key423, -1), (key422, -1), (key422, 1), (key412, 1), (key586, 2), (key586, -1), (key580, -1), (key265, -1), (key264, -1), (key264, 1), (key254, 1), (key333, 1), (key332, 1), (key332, -1), (key322, -1), (key610, -1), (key604, -1), (key610, 1), (key598, 1), (key274, 2), (key274, -1), (key269, -1), (key343, -2), (key343, 1), (key337, 1), (key484, 1), (key478, 1), (key484, -1), (key472, -1)]

def rawRow266 : Integer.Sparse Key := [(key391, -1), (key570, -1), (key391, 2), (key401, 1), (key575, 1), (key308, -1), (key401, -1), (key402, -2), (key310, 1), (key402, 1), (key412, 1), (key580, 1), (key412, -2), (key422, -1), (key586, -1), (key242, 1), (key422, 1), (key423, 2), (key244, -1), (key423, -1), (key446, -1), (key598, -1), (key322, 1), (key446, 1), (key454, 1), (key604, 1), (key254, -1), (key454, -1), (key333, -1), (key462, -1), (key265, 1), (key462, 1), (key472, 2), (key337, -1), (key472, -1), (key478, -2), (key269, 1), (key478, 1), (key343, 1), (key484, 1), (key274, -1), (key484, -1)]

def rawRow267 : Integer.Sparse Key := [(key570, -1), (key391, -1), (key391, 2), (key575, 1), (key401, 1), (key401, -1), (key308, -1), (key402, -2), (key402, 1), (key310, 1), (key580, 1), (key412, 1), (key412, -2), (key586, -1), (key422, -1), (key422, 1), (key242, 1), (key423, 2), (key423, -1), (key244, -1), (key598, -1), (key446, -1), (key446, 1), (key322, 1), (key604, 1), (key454, 1), (key454, -1), (key254, -1), (key462, -1), (key333, -1), (key462, 1), (key265, 1), (key472, 2), (key472, -1), (key337, -1), (key478, -2), (key478, 1), (key269, 1), (key484, 1), (key343, 1), (key484, -1), (key274, -1)]

def rawRow268 : Integer.Sparse Key := [(key401, -1), (key402, -1), (key575, 2), (key308, 1), (key310, 1), (key570, -1), (key575, -1), (key308, -2), (key391, 1), (key401, 1), (key422, 1), (key423, 1), (key586, -2), (key242, -1), (key244, -1), (key580, 1), (key586, 1), (key242, 2), (key412, -1), (key422, -1), (key332, -1), (key333, -1), (key604, 1), (key610, 1), (key264, 1), (key265, 1), (key598, -1), (key610, -1), (key254, -1), (key264, -1), (key322, 1), (key332, 1), (key343, 2), (key478, -1), (key484, -1), (key274, -2), (key472, 1), (key484, 1), (key269, 1), (key274, 1), (key337, -1), (key343, -1)]

def rawRow269 : Integer.Sparse Key := [(key402, -1), (key401, -1), (key575, 2), (key310, 1), (key308, 1), (key575, -1), (key570, -1), (key308, -2), (key401, 1), (key391, 1), (key423, 1), (key422, 1), (key586, -2), (key244, -1), (key242, -1), (key586, 1), (key580, 1), (key242, 2), (key422, -1), (key412, -1), (key333, -1), (key332, -1), (key610, 1), (key604, 1), (key265, 1), (key264, 1), (key610, -1), (key598, -1), (key264, -1), (key254, -1), (key332, 1), (key322, 1), (key343, 2), (key484, -1), (key478, -1), (key274, -2), (key484, 1), (key472, 1), (key274, 1), (key269, 1), (key343, -1), (key337, -1)]

def rawRow270 : Integer.Sparse Key := [(key401, -1), (key575, -1), (key402, 2), (key391, 1), (key570, 1), (key310, -1), (key402, -1), (key391, -2), (key308, 1), (key401, 1), (key422, 1), (key586, 1), (key423, -2), (key412, -1), (key580, -1), (key244, 1), (key423, 1), (key412, 2), (key242, -1), (key422, -1), (key454, -1), (key604, -1), (key333, 1), (key462, 1), (key446, 1), (key598, 1), (key265, -1), (key462, -1), (key322, -1), (key446, -1), (key254, 1), (key454, 1), (key478, 2), (key343, -1), (key484, -1), (key472, -2), (key274, 1), (key484, 1), (key337, 1), (key472, 1), (key269, -1), (key478, -1)]

def rawRow271 : Integer.Sparse Key := [(key575, -1), (key401, -1), (key402, 2), (key570, 1), (key391, 1), (key402, -1), (key310, -1), (key391, -2), (key401, 1), (key308, 1), (key586, 1), (key422, 1), (key423, -2), (key580, -1), (key412, -1), (key423, 1), (key244, 1), (key412, 2), (key422, -1), (key242, -1), (key604, -1), (key454, -1), (key462, 1), (key333, 1), (key598, 1), (key446, 1), (key462, -1), (key265, -1), (key446, -1), (key322, -1), (key454, 1), (key254, 1), (key478, 2), (key484, -1), (key343, -1), (key472, -2), (key484, 1), (key274, 1), (key472, 1), (key337, 1), (key478, -1), (key269, -1)]

def rawRow273 : Integer.Sparse Key := [(key322, -1), (key337, -1), (key322, 2), (key446, 1), (key472, 1), (key412, -1), (key446, -1), (key598, -2), (key580, 1), (key598, 1), (key254, 1), (key269, 1), (key254, -2), (key454, -1), (key478, -1), (key391, 1), (key454, 1), (key604, 2), (key570, -1), (key604, -1), (key264, -1), (key274, -1), (key242, 1), (key264, 1), (key332, 1), (key343, 1), (key308, -1), (key332, -1), (key586, -1), (key610, -1), (key575, 1), (key610, 1), (key265, 2), (key244, -1), (key265, -1), (key333, -2), (key310, 1), (key333, 1), (key423, 1), (key462, 1), (key402, -1), (key462, -1)]

def rawRow274 : Integer.Sparse Key := [(key337, -1), (key322, -1), (key322, 2), (key472, 1), (key446, 1), (key446, -1), (key412, -1), (key598, -2), (key598, 1), (key580, 1), (key269, 1), (key254, 1), (key254, -2), (key478, -1), (key454, -1), (key454, 1), (key391, 1), (key604, 2), (key604, -1), (key570, -1), (key274, -1), (key264, -1), (key264, 1), (key242, 1), (key343, 1), (key332, 1), (key332, -1), (key308, -1), (key610, -1), (key586, -1), (key610, 1), (key575, 1), (key265, 2), (key265, -1), (key244, -1), (key333, -2), (key333, 1), (key310, 1), (key462, 1), (key423, 1), (key462, -1), (key402, -1)]

def rawRow276 : Integer.Sparse Key := [(key412, -1), (key580, -1), (key412, 2), (key446, 1), (key598, 1), (key322, -1), (key446, -1), (key472, -2), (key337, 1), (key472, 1), (key391, 1), (key570, 1), (key391, -2), (key454, -1), (key604, -1), (key254, 1), (key454, 1), (key478, 2), (key269, -1), (key478, -1), (key401, -1), (key575, -1), (key308, 1), (key401, 1), (key422, 1), (key586, 1), (key242, -1), (key422, -1), (key343, -1), (key484, -1), (key274, 1), (key484, 1), (key402, 2), (key310, -1), (key402, -1), (key423, -2), (key244, 1), (key423, 1), (key333, 1), (key462, 1), (key265, -1), (key462, -1)]

def rawRow277 : Integer.Sparse Key := [(key580, -1), (key412, -1), (key412, 2), (key598, 1), (key446, 1), (key446, -1), (key322, -1), (key472, -2), (key472, 1), (key337, 1), (key570, 1), (key391, 1), (key391, -2), (key604, -1), (key454, -1), (key454, 1), (key254, 1), (key478, 2), (key478, -1), (key269, -1), (key575, -1), (key401, -1), (key401, 1), (key308, 1), (key586, 1), (key422, 1), (key422, -1), (key242, -1), (key484, -1), (key343, -1), (key484, 1), (key274, 1), (key402, 2), (key402, -1), (key310, -1), (key423, -2), (key423, 1), (key244, 1), (key462, 1), (key333, 1), (key462, -1), (key265, -1)]

def rawRow278 : Integer.Sparse Key := [(key446, -1), (key472, -1), (key598, 2), (key322, 1), (key337, 1), (key580, -1), (key598, -1), (key322, -2), (key412, 1), (key446, 1), (key454, 1), (key478, 1), (key604, -2), (key254, -1), (key269, -1), (key570, 1), (key604, 1), (key254, 2), (key391, -1), (key454, -1), (key332, -1), (key343, -1), (key586, 1), (key610, 1), (key264, 1), (key274, 1), (key575, -1), (key610, -1), (key242, -1), (key264, -1), (key308, 1), (key332, 1), (key333, 2), (key423, -1), (key462, -1), (key265, -2), (key402, 1), (key462, 1), (key244, 1), (key265, 1), (key310, -1), (key333, -1)]

def rawRow279 : Integer.Sparse Key := [(key472, -1), (key446, -1), (key598, 2), (key337, 1), (key322, 1), (key598, -1), (key580, -1), (key322, -2), (key446, 1), (key412, 1), (key478, 1), (key454, 1), (key604, -2), (key269, -1), (key254, -1), (key604, 1), (key570, 1), (key254, 2), (key454, -1), (key391, -1), (key343, -1), (key332, -1), (key610, 1), (key586, 1), (key274, 1), (key264, 1), (key610, -1), (key575, -1), (key264, -1), (key242, -1), (key332, 1), (key308, 1), (key333, 2), (key462, -1), (key423, -1), (key265, -2), (key462, 1), (key402, 1), (key265, 1), (key244, 1), (key333, -1), (key310, -1)]

def rawRow280 : Integer.Sparse Key := [(key446, -1), (key598, -1), (key472, 2), (key412, 1), (key580, 1), (key337, -1), (key472, -1), (key412, -2), (key322, 1), (key446, 1), (key454, 1), (key604, 1), (key478, -2), (key391, -1), (key570, -1), (key269, 1), (key478, 1), (key391, 2), (key254, -1), (key454, -1), (key422, -1), (key586, -1), (key343, 1), (key484, 1), (key401, 1), (key575, 1), (key274, -1), (key484, -1), (key308, -1), (key401, -1), (key242, 1), (key422, 1), (key423, 2), (key333, -1), (key462, -1), (key402, -2), (key265, 1), (key462, 1), (key310, 1), (key402, 1), (key244, -1), (key423, -1)]

def rawRow281 : Integer.Sparse Key := [(key598, -1), (key446, -1), (key472, 2), (key580, 1), (key412, 1), (key472, -1), (key337, -1), (key412, -2), (key446, 1), (key322, 1), (key604, 1), (key454, 1), (key478, -2), (key570, -1), (key391, -1), (key478, 1), (key269, 1), (key391, 2), (key454, -1), (key254, -1), (key586, -1), (key422, -1), (key484, 1), (key343, 1), (key575, 1), (key401, 1), (key484, -1), (key274, -1), (key401, -1), (key308, -1), (key422, 1), (key242, 1), (key423, 2), (key462, -1), (key333, -1), (key402, -2), (key462, 1), (key265, 1), (key402, 1), (key310, 1), (key423, -1), (key244, -1)]

def rawRow282 : Integer.Sparse Key := [(key332, -1), (key333, -1), (key343, 2), (key422, 1), (key423, 1), (key478, -1), (key484, -1), (key586, -2), (key604, 1), (key610, 1), (key264, 1), (key265, 1), (key274, -2), (key401, -1), (key402, -1), (key472, 1), (key484, 1), (key575, 2), (key598, -1), (key610, -1), (key242, -1), (key244, -1), (key269, 1), (key274, 1), (key308, 1), (key310, 1), (key337, -1), (key343, -1), (key570, -1), (key575, -1), (key580, 1), (key586, 1), (key242, 2), (key254, -1), (key264, -1), (key308, -2), (key322, 1), (key332, 1), (key391, 1), (key401, 1), (key412, -1), (key422, -1)]

def rawRow283 : Integer.Sparse Key := [(key333, -1), (key332, -1), (key343, 2), (key423, 1), (key422, 1), (key484, -1), (key478, -1), (key586, -2), (key610, 1), (key604, 1), (key265, 1), (key264, 1), (key274, -2), (key402, -1), (key401, -1), (key484, 1), (key472, 1), (key575, 2), (key610, -1), (key598, -1), (key244, -1), (key242, -1), (key274, 1), (key269, 1), (key310, 1), (key308, 1), (key343, -1), (key337, -1), (key575, -1), (key570, -1), (key586, 1), (key580, 1), (key242, 2), (key264, -1), (key254, -1), (key308, -2), (key332, 1), (key322, 1), (key401, 1), (key391, 1), (key422, -1), (key412, -1)]

def rawRow284 : Integer.Sparse Key := [(key332, -1), (key343, -1), (key333, 2), (key454, 1), (key478, 1), (key423, -1), (key462, -1), (key604, -2), (key586, 1), (key610, 1), (key264, 1), (key274, 1), (key265, -2), (key446, -1), (key472, -1), (key402, 1), (key462, 1), (key598, 2), (key575, -1), (key610, -1), (key254, -1), (key269, -1), (key244, 1), (key265, 1), (key322, 1), (key337, 1), (key310, -1), (key333, -1), (key580, -1), (key598, -1), (key570, 1), (key604, 1), (key254, 2), (key242, -1), (key264, -1), (key322, -2), (key308, 1), (key332, 1), (key412, 1), (key446, 1), (key391, -1), (key454, -1)]

def rawRow285 : Integer.Sparse Key := [(key343, -1), (key332, -1), (key333, 2), (key478, 1), (key454, 1), (key462, -1), (key423, -1), (key604, -2), (key610, 1), (key586, 1), (key274, 1), (key264, 1), (key265, -2), (key472, -1), (key446, -1), (key462, 1), (key402, 1), (key598, 2), (key610, -1), (key575, -1), (key269, -1), (key254, -1), (key265, 1), (key244, 1), (key337, 1), (key322, 1), (key333, -1), (key310, -1), (key598, -1), (key580, -1), (key604, 1), (key570, 1), (key254, 2), (key264, -1), (key242, -1), (key322, -2), (key332, 1), (key308, 1), (key446, 1), (key412, 1), (key454, -1), (key391, -1)]

def rawRow286 : Integer.Sparse Key := [(key422, -1), (key423, -1), (key586, 2), (key332, 1), (key333, 1), (key604, -1), (key610, -1), (key343, -2), (key478, 1), (key484, 1), (key401, 1), (key402, 1), (key575, -2), (key264, -1), (key265, -1), (key598, 1), (key610, 1), (key274, 2), (key472, -1), (key484, -1), (key308, -1), (key310, -1), (key570, 1), (key575, 1), (key242, 1), (key244, 1), (key580, -1), (key586, -1), (key269, -1), (key274, -1), (key337, 1), (key343, 1), (key308, 2), (key391, -1), (key401, -1), (key242, -2), (key412, 1), (key422, 1), (key254, 1), (key264, 1), (key322, -1), (key332, -1)]

def rawRow287 : Integer.Sparse Key := [(key423, -1), (key422, -1), (key586, 2), (key333, 1), (key332, 1), (key610, -1), (key604, -1), (key343, -2), (key484, 1), (key478, 1), (key402, 1), (key401, 1), (key575, -2), (key265, -1), (key264, -1), (key610, 1), (key598, 1), (key274, 2), (key484, -1), (key472, -1), (key310, -1), (key308, -1), (key575, 1), (key570, 1), (key244, 1), (key242, 1), (key586, -1), (key580, -1), (key274, -1), (key269, -1), (key343, 1), (key337, 1), (key308, 2), (key401, -1), (key391, -1), (key242, -2), (key422, 1), (key412, 1), (key264, 1), (key254, 1), (key332, -1), (key322, -1)]

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

def rawRow288 : Integer.Sparse Key := [(key422, -1), (key586, -1), (key423, 2), (key454, 1), (key604, 1), (key333, -1), (key462, -1), (key478, -2), (key343, 1), (key484, 1), (key401, 1), (key575, 1), (key402, -2), (key446, -1), (key598, -1), (key265, 1), (key462, 1), (key472, 2), (key274, -1), (key484, -1), (key391, -1), (key570, -1), (key310, 1), (key402, 1), (key412, 1), (key580, 1), (key244, -1), (key423, -1), (key337, -1), (key472, -1), (key269, 1), (key478, 1), (key391, 2), (key308, -1), (key401, -1), (key412, -2), (key242, 1), (key422, 1), (key322, 1), (key446, 1), (key254, -1), (key454, -1)]

def rawRow289 : Integer.Sparse Key := [(key586, -1), (key422, -1), (key423, 2), (key604, 1), (key454, 1), (key462, -1), (key333, -1), (key478, -2), (key484, 1), (key343, 1), (key575, 1), (key401, 1), (key402, -2), (key598, -1), (key446, -1), (key462, 1), (key265, 1), (key472, 2), (key484, -1), (key274, -1), (key570, -1), (key391, -1), (key402, 1), (key310, 1), (key580, 1), (key412, 1), (key423, -1), (key244, -1), (key472, -1), (key337, -1), (key478, 1), (key269, 1), (key391, 2), (key401, -1), (key308, -1), (key412, -2), (key422, 1), (key242, 1), (key446, 1), (key322, 1), (key454, -1), (key254, -1)]

def rawRow290 : Integer.Sparse Key := [(key454, -1), (key478, -1), (key604, 2), (key332, 1), (key343, 1), (key586, -1), (key610, -1), (key333, -2), (key423, 1), (key462, 1), (key446, 1), (key472, 1), (key598, -2), (key264, -1), (key274, -1), (key575, 1), (key610, 1), (key265, 2), (key402, -1), (key462, -1), (key322, -1), (key337, -1), (key580, 1), (key598, 1), (key254, 1), (key269, 1), (key570, -1), (key604, -1), (key244, -1), (key265, -1), (key310, 1), (key333, 1), (key322, 2), (key412, -1), (key446, -1), (key254, -2), (key391, 1), (key454, 1), (key242, 1), (key264, 1), (key308, -1), (key332, -1)]

def rawRow291 : Integer.Sparse Key := [(key478, -1), (key454, -1), (key604, 2), (key343, 1), (key332, 1), (key610, -1), (key586, -1), (key333, -2), (key462, 1), (key423, 1), (key472, 1), (key446, 1), (key598, -2), (key274, -1), (key264, -1), (key610, 1), (key575, 1), (key265, 2), (key462, -1), (key402, -1), (key337, -1), (key322, -1), (key598, 1), (key580, 1), (key269, 1), (key254, 1), (key604, -1), (key570, -1), (key265, -1), (key244, -1), (key333, 1), (key310, 1), (key322, 2), (key446, -1), (key412, -1), (key254, -2), (key454, 1), (key391, 1), (key264, 1), (key242, 1), (key332, -1), (key308, -1)]

def rawRow292 : Integer.Sparse Key := [(key454, -1), (key604, -1), (key478, 2), (key422, 1), (key586, 1), (key343, -1), (key484, -1), (key423, -2), (key333, 1), (key462, 1), (key446, 1), (key598, 1), (key472, -2), (key401, -1), (key575, -1), (key274, 1), (key484, 1), (key402, 2), (key265, -1), (key462, -1), (key412, -1), (key580, -1), (key337, 1), (key472, 1), (key391, 1), (key570, 1), (key269, -1), (key478, -1), (key310, -1), (key402, -1), (key244, 1), (key423, 1), (key412, 2), (key322, -1), (key446, -1), (key391, -2), (key254, 1), (key454, 1), (key308, 1), (key401, 1), (key242, -1), (key422, -1)]

def rawRow293 : Integer.Sparse Key := [(key604, -1), (key454, -1), (key478, 2), (key586, 1), (key422, 1), (key484, -1), (key343, -1), (key423, -2), (key462, 1), (key333, 1), (key598, 1), (key446, 1), (key472, -2), (key575, -1), (key401, -1), (key484, 1), (key274, 1), (key402, 2), (key462, -1), (key265, -1), (key580, -1), (key412, -1), (key472, 1), (key337, 1), (key570, 1), (key391, 1), (key478, -1), (key269, -1), (key402, -1), (key310, -1), (key423, 1), (key244, 1), (key412, 2), (key446, -1), (key322, -1), (key391, -2), (key454, 1), (key254, 1), (key401, 1), (key308, 1), (key422, -1), (key242, -1)]

def rawRow295 : Integer.Sparse Key := [(key1305, -2), (key1301, 1), (key1305, 1), (key1332, 2), (key1321, -1), (key1332, -1), (key1348, -1), (key1349, -1), (key1342, 1), (key1349, 1), (key1400, 2), (key1396, -1), (key1400, -1), (key1450, -2), (key1429, 1), (key1450, 1), (key1469, 1), (key1470, 1), (key1460, -1), (key1470, -1), (key1562, -2), (key1551, 1), (key1562, 1), (key1599, 2), (key1578, -1), (key1599, -1), (key1670, -1), (key1676, -1), (key1662, 1), (key1676, 1), (key1783, 1), (key1784, 1), (key1777, -1), (key1784, -1), (key1801, -1), (key1802, -1), (key1793, 1), (key1802, 1), (key1828, 1), (key1834, 1), (key1820, -1), (key1834, -1)]

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

def rawRow7449 : Integer.Sparse Key := [(key1024, -24), (key1102, 6), (key1102, 6), (key1102, 6), (key989, 6)]

end MUB6.Certificate.GramRows

end OAI
end


