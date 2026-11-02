-- Prove2me | Definitions.Def_OAIQ106D100
-- name    : OAIQ106D100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:01:35.343481+00:00
-- url     : https://prove2.me/theorems/9dce72dd-dfed-4ca6-8557-084103bff0d2
-- title:
--   Definitions bundle OAIQ106D100 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 451 declarations of OpenAI's Lean: 451 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow2249`, `OAI.MUB6.Certificate.GramRows.rawRow225`, `OAI.MUB6.Certificate.GramRows.rawRow2250`, `OAI.MUB6.Certificate.GramRows.rawRow2251`, `OAI.MUB6.Certificate.GramRows.rawRow2252`, `OAI.MUB6.Certificate.GramRows.rawRow2253`, `OAI.MUB6.Certificate.GramRows.rawRow2254`, `OAI.MUB6.Certificate.GramRows.rawRow2255`, `OAI.MUB6.Certificate.GramRows.rawRow2256`, `OAI.MUB6.Certificate.GramRows.rawRow2257`, `OAI.MUB6.Certificate.GramRows.rawRow2258`, `OAI.MUB6.Certificate.GramRows.rawRow2259`, `OAI.MUB6.Certificate.GramRows.rawRow226`, `OAI.MUB6.Certificate.GramRows.rawRow2260`, `OAI.MUB6.Certificate.GramRows.rawRow2261`, `OAI.MUB6.Certificate.GramRows.rawRow2262`, `OAI.MUB6.Certificate.GramRows.rawRow2263`, `OAI.MUB6.Certificate.GramRows.rawRow2264`, `OAI.MUB6.Certificate.GramRows.rawRow2265`, `OAI.MUB6.Certificate.GramRows.rawRow2267`, `OAI.MUB6.Certificate.GramRows.rawRow2268`, `OAI.MUB6.Certificate.GramRows.rawRow227`, `OAI.MUB6.Certificate.GramRows.rawRow2275`, `OAI.MUB6.Certificate.GramRows.rawRow2276`, `OAI.MUB6.Certificate.GramRows.rawRow2277`, `OAI.MUB6.Certificate.GramRows.rawRow228`, `OAI.MUB6.Certificate.GramRows.rawRow229`, `OAI.MUB6.Certificate.GramRows.rawRow2296`, `OAI.MUB6.Certificate.GramRows.rawRow2297`, `OAI.MUB6.Certificate.GramRows.rawRow2298`, `OAI.MUB6.Certificate.GramRows.rawRow2299`, `OAI.MUB6.Certificate.GramRows.rawRow230`, `OAI.MUB6.Certificate.GramRows.rawRow2300`, `OAI.MUB6.Certificate.GramRows.rawRow2301`, `OAI.MUB6.Certificate.GramRows.rawRow2302`, `OAI.MUB6.Certificate.GramRows.rawRow2303`, `OAI.MUB6.Certificate.GramRows.rawRow2304`, `OAI.MUB6.Certificate.GramRows.rawRow2305`, `OAI.MUB6.Certificate.GramRows.rawRow2306`, `OAI.MUB6.Certificate.GramRows.rawRow2307` and 411 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block4`, `MutuallyUnbiased_GramRows_Block41`, `MutuallyUnbiased_GramRows_Block42`, `MutuallyUnbiased_GramRows_Block43`, `MutuallyUnbiased_GramRows_Block44`, `MutuallyUnbiased_GramRows_Block45`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block48`, `MutuallyUnbiased_GramRows_Block49`, `MutuallyUnbiased_GramRows_Block5`, `MutuallyUnbiased_GramRows_Block50`, `MutuallyUnbiased_GramRows_Block51`, `MutuallyUnbiased_GramRows_Block6`, `MutuallyUnbiased_GramRows_Block7`, `MutuallyUnbiased_MixedSemantics_Values18`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D209`, `OAIQ106D210`, `OAIQ106D211`, `OAIQ106D215` and `OAIQ106D217`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval12_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_12`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval16_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval18_9`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow26 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key406, 2), (key467, 1), (key475, 1), (key385, -1), (key435, -1), (key469, -2), (key397, 1), (key442, 1), (key319, 1), (key328, 1), (key316, -2), (key593, -1), (key601, -1), (key248, 1), (key435, 1), (key595, 2), (key260, -1), (key442, -1), (key335, -1), (key340, -1), (key302, 1), (key316, 1), (key578, 1), (key583, 1), (key236, -1), (key406, -1), (key340, -1), (key475, -1), (key271, 1), (key469, 1), (key397, 2), (key305, -1), (key388, -1), (key418, -2), (key239, 1), (key409, 1), (key328, 1), (key450, 1), (key260, -1), (key442, -1)]

def rawRow27 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key406, 2), (key475, 1), (key467, 1), (key435, -1), (key385, -1), (key469, -2), (key442, 1), (key397, 1), (key328, 1), (key319, 1), (key316, -2), (key601, -1), (key593, -1), (key435, 1), (key248, 1), (key595, 2), (key442, -1), (key260, -1), (key340, -1), (key335, -1), (key316, 1), (key302, 1), (key583, 1), (key578, 1), (key406, -1), (key236, -1), (key475, -1), (key340, -1), (key469, 1), (key271, 1), (key397, 2), (key388, -1), (key305, -1), (key418, -2), (key409, 1), (key239, 1), (key450, 1), (key328, 1), (key442, -1), (key260, -1)]

def rawRow30 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key469, 2), (key409, 1), (key418, 1), (key397, -1), (key442, -1), (key406, -2), (key385, 1), (key435, 1), (key593, 1), (key601, 1), (key595, -2), (key319, -1), (key328, -1), (key260, 1), (key442, 1), (key316, 2), (key248, -1), (key435, -1), (key578, -1), (key583, -1), (key572, 1), (key595, 1), (key335, 1), (key340, 1), (key271, -1), (key469, -1), (key302, -1), (key316, -1), (key236, 1), (key406, 1), (key418, 2), (key328, -1), (key450, -1), (key397, -2), (key260, 1), (key442, 1), (key305, 1), (key388, 1), (key239, -1), (key409, -1)]

def rawRow31 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key469, 2), (key418, 1), (key409, 1), (key442, -1), (key397, -1), (key406, -2), (key435, 1), (key385, 1), (key601, 1), (key593, 1), (key595, -2), (key328, -1), (key319, -1), (key442, 1), (key260, 1), (key316, 2), (key435, -1), (key248, -1), (key583, -1), (key578, -1), (key595, 1), (key572, 1), (key340, 1), (key335, 1), (key469, -1), (key271, -1), (key316, -1), (key302, -1), (key406, 1), (key236, 1), (key418, 2), (key450, -1), (key328, -1), (key397, -2), (key442, 1), (key260, 1), (key388, 1), (key305, 1), (key409, -1), (key239, -1)]

def rawRow32 : Integer.Sparse Key := [(key568, -1), (key568, -1), (key572, 2), (key578, 1), (key578, 1), (key595, -1), (key595, -1), (key583, -2), (key601, 1), (key601, 1), (key267, 1), (key267, 1), (key271, -2), (key335, -1), (key335, -1), (key469, 1), (key469, 1), (key340, 2), (key475, -1), (key475, -1), (key239, -1), (key239, -1), (key260, 1), (key260, 1), (key305, 1), (key305, 1), (key397, -1), (key397, -1), (key328, -1), (key328, -1), (key418, 1), (key418, 1), (key236, 2), (key248, -1), (key248, -1), (key302, -2), (key316, 1), (key316, 1), (key385, 1), (key385, 1), (key406, -1), (key406, -1)]

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

def rawRow225 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2698, 2), (key2752, 1), (key2757, 1), (key2663, -1), (key2698, -1), (key2752, -2), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2801, -2), (key3011, -1), (key3016, -1), (key2608, 1), (key2801, 1), (key2827, 2), (key2614, -1), (key2807, -1), (key2858, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key2868, 1), (key3025, 1), (key2624, -1), (key2851, -1), (key2724, -1), (key2868, -1), (key2638, 1), (key2858, 1), (key2919, 2), (key2752, -1), (key2918, -1), (key2922, -2), (key2657, 1), (key2918, 1), (key2757, 1), (key2922, 1), (key2659, -1), (key2919, -1)]

def rawRow226 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2698, 2), (key2757, 1), (key2752, 1), (key2698, -1), (key2663, -1), (key2752, -2), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2801, -2), (key3016, -1), (key3011, -1), (key2801, 1), (key2608, 1), (key2827, 2), (key2807, -1), (key2614, -1), (key3022, -1), (key2858, -1), (key2851, 1), (key2698, 1), (key3025, 1), (key2868, 1), (key2851, -1), (key2624, -1), (key2868, -1), (key2724, -1), (key2858, 1), (key2638, 1), (key2919, 2), (key2918, -1), (key2752, -1), (key2922, -2), (key2918, 1), (key2657, 1), (key2922, 1), (key2757, 1), (key2919, -1), (key2659, -1)]

def rawRow227 : Integer.Sparse Key := [(key2752, -1), (key2752, -1), (key2757, 2), (key2669, 1), (key2669, 1), (key2724, -1), (key2724, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key3011, 1), (key3011, 1), (key3016, -2), (key2614, -1), (key2614, -1), (key2827, 1), (key2827, 1), (key2608, 2), (key2801, -1), (key2801, -1), (key2724, -1), (key2724, -1), (key3025, 1), (key3025, 1), (key2638, 1), (key2638, 1), (key3022, -1), (key3022, -1), (key2624, -1), (key2624, -1), (key2698, 1), (key2698, 1), (key2757, 2), (key2922, -1), (key2922, -1), (key2659, -2), (key2919, 1), (key2919, 1), (key2657, 1), (key2657, 1), (key2752, -1), (key2752, -1)]

def rawRow228 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2752, 2), (key2704, 1), (key2724, 1), (key2669, -1), (key2704, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key3011, -2), (key2807, -1), (key2827, -1), (key2614, 1), (key2807, 1), (key2801, 2), (key2608, -1), (key2801, -1), (key2868, -1), (key3025, -1), (key2724, 1), (key2868, 1), (key2858, 1), (key3022, 1), (key2638, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key2624, 1), (key2851, 1), (key2922, 2), (key2757, -1), (key2922, -1), (key2919, -2), (key2659, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2657, -1), (key2918, -1)]

def rawRow229 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2752, 2), (key2724, 1), (key2704, 1), (key2704, -1), (key2669, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key3011, -2), (key2827, -1), (key2807, -1), (key2807, 1), (key2614, 1), (key2801, 2), (key2801, -1), (key2608, -1), (key3025, -1), (key2868, -1), (key2868, 1), (key2724, 1), (key3022, 1), (key2858, 1), (key2858, -1), (key2638, -1), (key2851, -1), (key2698, -1), (key2851, 1), (key2624, 1), (key2922, 2), (key2922, -1), (key2757, -1), (key2919, -2), (key2919, 1), (key2659, 1), (key2918, 1), (key2752, 1), (key2918, -1), (key2657, -1)]

def rawRow230 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, 1), (key2858, -1), (key2919, -1), (key2827, -2), (key2868, 1), (key2922, 1), (key2624, 1), (key2630, 1), (key2638, -2), (key2698, -1), (key2704, -1), (key2858, 1), (key3022, 1), (key2724, 2), (key2868, -1), (key3025, -1), (key2608, -1), (key2614, -1), (key2657, 1), (key2659, 1), (key2663, 1), (key2669, 1), (key2752, -1), (key2757, -1), (key3007, -1), (key3009, -1), (key3011, 1), (key3016, 1), (key2614, 2), (key2630, -1), (key2638, -1), (key2669, -2), (key2704, 1), (key2724, 1), (key2784, 1), (key2792, 1), (key2807, -1), (key2827, -1)]

def rawRow231 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2792, 2), (key2807, 1), (key2801, 1), (key2919, -1), (key2858, -1), (key2827, -2), (key2922, 1), (key2868, 1), (key2630, 1), (key2624, 1), (key2638, -2), (key2704, -1), (key2698, -1), (key3022, 1), (key2858, 1), (key2724, 2), (key3025, -1), (key2868, -1), (key2614, -1), (key2608, -1), (key2659, 1), (key2657, 1), (key2669, 1), (key2663, 1), (key2757, -1), (key2752, -1), (key3009, -1), (key3007, -1), (key3016, 1), (key3011, 1), (key2614, 2), (key2638, -1), (key2630, -1), (key2669, -2), (key2724, 1), (key2704, 1), (key2792, 1), (key2784, 1), (key2827, -1), (key2807, -1)]

def rawRow232 : Integer.Sparse Key := [(key2784, -1), (key2792, -1), (key2778, 2), (key2918, 1), (key2919, 1), (key2801, -1), (key2851, -1), (key2922, -2), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2624, -2), (key3021, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key3025, 2), (key2724, -1), (key2868, -1), (key2657, -1), (key2659, -1), (key2608, 1), (key2624, 1), (key2724, 1), (key2757, 1), (key2663, -1), (key2698, -1), (key3016, -1), (key3025, -1), (key3009, 1), (key3022, 1), (key2638, 2), (key2614, -1), (key2630, -1), (key2724, -2), (key2669, 1), (key2704, 1), (key2827, 1), (key2868, 1), (key2792, -1), (key2858, -1)]

def rawRow233 : Integer.Sparse Key := [(key2792, -1), (key2784, -1), (key2778, 2), (key2919, 1), (key2918, 1), (key2851, -1), (key2801, -1), (key2922, -2), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2624, -2), (key3022, -1), (key3021, -1), (key2851, 1), (key2698, 1), (key3025, 2), (key2868, -1), (key2724, -1), (key2659, -1), (key2657, -1), (key2624, 1), (key2608, 1), (key2757, 1), (key2724, 1), (key2698, -1), (key2663, -1), (key3025, -1), (key3016, -1), (key3022, 1), (key3009, 1), (key2638, 2), (key2630, -1), (key2614, -1), (key2724, -2), (key2704, 1), (key2669, 1), (key2868, 1), (key2827, 1), (key2858, -1), (key2792, -1)]

def rawRow234 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2827, 2), (key2778, 1), (key2784, 1), (key2868, -1), (key2922, -1), (key2792, -2), (key2858, 1), (key2919, 1), (key2698, 1), (key2704, 1), (key2724, -2), (key2624, -1), (key2630, -1), (key2868, 1), (key3025, 1), (key2638, 2), (key2858, -1), (key3022, -1), (key2663, -1), (key2669, -1), (key2724, 1), (key2757, 1), (key2608, 1), (key2614, 1), (key3011, -1), (key3016, -1), (key2657, -1), (key2659, -1), (key2752, 1), (key2757, 1), (key2669, 2), (key2784, -1), (key2792, -1), (key2614, -2), (key2807, 1), (key2827, 1), (key2630, 1), (key2638, 1), (key2704, -1), (key2724, -1)]

def rawRow235 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, 2), (key2784, 1), (key2778, 1), (key2922, -1), (key2868, -1), (key2792, -2), (key2919, 1), (key2858, 1), (key2704, 1), (key2698, 1), (key2724, -2), (key2630, -1), (key2624, -1), (key3025, 1), (key2868, 1), (key2638, 2), (key3022, -1), (key2858, -1), (key2669, -1), (key2663, -1), (key2757, 1), (key2724, 1), (key2614, 1), (key2608, 1), (key3016, -1), (key3011, -1), (key2659, -1), (key2657, -1), (key2757, 1), (key2752, 1), (key2669, 2), (key2792, -1), (key2784, -1), (key2614, -2), (key2827, 1), (key2807, 1), (key2638, 1), (key2630, 1), (key2724, -1), (key2704, -1)]

def rawRow236 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2801, 2), (key2918, 1), (key2922, 1), (key2778, -1), (key2851, -1), (key2919, -2), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2698, -2), (key3021, -1), (key3025, -1), (key2624, 1), (key2851, 1), (key3022, 2), (key2638, -1), (key2858, -1), (key2752, -1), (key2757, -1), (key2663, 1), (key2698, 1), (key3011, 1), (key3016, 1), (key2608, -1), (key2801, -1), (key2757, -1), (key2922, -1), (key2659, 1), (key2919, 1), (key2792, 2), (key2669, -1), (key2784, -1), (key2827, -2), (key2614, 1), (key2807, 1), (key2724, 1), (key2868, 1), (key2638, -1), (key2858, -1)]

def rawRow237 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2801, 2), (key2922, 1), (key2918, 1), (key2851, -1), (key2778, -1), (key2919, -2), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2698, -2), (key3025, -1), (key3021, -1), (key2851, 1), (key2624, 1), (key3022, 2), (key2858, -1), (key2638, -1), (key2757, -1), (key2752, -1), (key2698, 1), (key2663, 1), (key3016, 1), (key3011, 1), (key2801, -1), (key2608, -1), (key2922, -1), (key2757, -1), (key2919, 1), (key2659, 1), (key2792, 2), (key2784, -1), (key2669, -1), (key2827, -2), (key2807, 1), (key2614, 1), (key2868, 1), (key2724, 1), (key2858, -1), (key2638, -1)]

def rawRow238 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2922, 2), (key2784, 1), (key2792, 1), (key2827, -1), (key2868, -1), (key2778, -2), (key2801, 1), (key2851, 1), (key3021, 1), (key3022, 1), (key3025, -2), (key2630, -1), (key2638, -1), (key2724, 1), (key2868, 1), (key2624, 2), (key2698, -1), (key2851, -1), (key3007, -1), (key3009, -1), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2757, -1), (key2922, -1), (key2608, -1), (key2624, -1), (key2663, 1), (key2698, 1), (key2724, 2), (key2827, -1), (key2868, -1), (key2638, -2), (key2792, 1), (key2858, 1), (key2614, 1), (key2630, 1), (key2669, -1), (key2704, -1)]

def rawRow239 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2922, 2), (key2792, 1), (key2784, 1), (key2868, -1), (key2827, -1), (key2778, -2), (key2851, 1), (key2801, 1), (key3022, 1), (key3021, 1), (key3025, -2), (key2638, -1), (key2630, -1), (key2868, 1), (key2724, 1), (key2624, 2), (key2851, -1), (key2698, -1), (key3009, -1), (key3007, -1), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2922, -1), (key2757, -1), (key2624, -1), (key2608, -1), (key2698, 1), (key2663, 1), (key2724, 2), (key2868, -1), (key2827, -1), (key2638, -2), (key2858, 1), (key2792, 1), (key2630, 1), (key2614, 1), (key2704, -1), (key2669, -1)]

def rawRow240 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2919, 2), (key2807, 1), (key2827, 1), (key2792, -1), (key2858, -1), (key2801, -2), (key2778, 1), (key2851, 1), (key3021, 1), (key3025, 1), (key3022, -2), (key2704, -1), (key2724, -1), (key2638, 1), (key2858, 1), (key2698, 2), (key2624, -1), (key2851, -1), (key3011, -1), (key3016, -1), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2659, -1), (key2919, -1), (key2663, -1), (key2698, -1), (key2608, 1), (key2801, 1), (key2827, 2), (key2724, -1), (key2868, -1), (key2792, -2), (key2638, 1), (key2858, 1), (key2669, 1), (key2784, 1), (key2614, -1), (key2807, -1)]

def rawRow241 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2919, 2), (key2827, 1), (key2807, 1), (key2858, -1), (key2792, -1), (key2801, -2), (key2851, 1), (key2778, 1), (key3025, 1), (key3021, 1), (key3022, -2), (key2724, -1), (key2704, -1), (key2858, 1), (key2638, 1), (key2698, 2), (key2851, -1), (key2624, -1), (key3016, -1), (key3011, -1), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2919, -1), (key2659, -1), (key2698, -1), (key2663, -1), (key2801, 1), (key2608, 1), (key2827, 2), (key2868, -1), (key2724, -1), (key2792, -2), (key2858, 1), (key2638, 1), (key2784, 1), (key2669, 1), (key2807, -1), (key2614, -1)]

def rawRow242 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3009, 2), (key3011, 1), (key3011, 1), (key3022, -1), (key3022, -1), (key3016, -2), (key3025, 1), (key3025, 1), (key2657, 1), (key2657, 1), (key2659, -2), (key2752, -1), (key2752, -1), (key2919, 1), (key2919, 1), (key2757, 2), (key2922, -1), (key2922, -1), (key2614, -1), (key2614, -1), (key2638, 1), (key2638, 1), (key2669, 1), (key2669, 1), (key2792, -1), (key2792, -1), (key2724, -1), (key2724, -1), (key2827, 1), (key2827, 1), (key2608, 2), (key2624, -1), (key2624, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

def rawRow243 : Integer.Sparse Key := [(key3007, -1), (key3009, -1), (key3007, 2), (key3021, 1), (key3022, 1), (key3011, -1), (key3021, -1), (key3025, -2), (key3016, 1), (key3025, 1), (key2657, 1), (key2659, 1), (key2657, -2), (key2918, -1), (key2919, -1), (key2752, 1), (key2918, 1), (key2922, 2), (key2757, -1), (key2922, -1), (key2630, -1), (key2638, -1), (key2614, 1), (key2630, 1), (key2784, 1), (key2792, 1), (key2669, -1), (key2784, -1), (key2827, -1), (key2868, -1), (key2724, 1), (key2868, 1), (key2624, 2), (key2608, -1), (key2624, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

def rawRow244 : Integer.Sparse Key := [(key3009, -1), (key3007, -1), (key3007, 2), (key3022, 1), (key3021, 1), (key3021, -1), (key3011, -1), (key3025, -2), (key3025, 1), (key3016, 1), (key2659, 1), (key2657, 1), (key2657, -2), (key2919, -1), (key2918, -1), (key2918, 1), (key2752, 1), (key2922, 2), (key2922, -1), (key2757, -1), (key2638, -1), (key2630, -1), (key2630, 1), (key2614, 1), (key2792, 1), (key2784, 1), (key2784, -1), (key2669, -1), (key2868, -1), (key2827, -1), (key2868, 1), (key2724, 1), (key2624, 2), (key2624, -1), (key2608, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

def rawRow245 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3016, 2), (key3007, 1), (key3007, 1), (key3025, -1), (key3025, -1), (key3009, -2), (key3022, 1), (key3022, 1), (key2752, 1), (key2752, 1), (key2757, -2), (key2657, -1), (key2657, -1), (key2922, 1), (key2922, 1), (key2659, 2), (key2919, -1), (key2919, -1), (key2669, -1), (key2669, -1), (key2724, 1), (key2724, 1), (key2614, 1), (key2614, 1), (key2827, -1), (key2827, -1), (key2638, -1), (key2638, -1), (key2792, 1), (key2792, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2608, -2), (key2801, 1), (key2801, 1), (key2624, 1), (key2624, 1), (key2698, -1), (key2698, -1)]

def rawRow246 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key3011, 2), (key3021, 1), (key3025, 1), (key3007, -1), (key3021, -1), (key3022, -2), (key3009, 1), (key3022, 1), (key2752, 1), (key2757, 1), (key2752, -2), (key2918, -1), (key2922, -1), (key2657, 1), (key2918, 1), (key2919, 2), (key2659, -1), (key2919, -1), (key2704, -1), (key2724, -1), (key2669, 1), (key2704, 1), (key2807, 1), (key2827, 1), (key2614, -1), (key2807, -1), (key2792, -1), (key2858, -1), (key2638, 1), (key2858, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, -2), (key2608, 1), (key2801, 1), (key2698, 1), (key2851, 1), (key2624, -1), (key2851, -1)]

def rawRow247 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key3011, 2), (key3025, 1), (key3021, 1), (key3021, -1), (key3007, -1), (key3022, -2), (key3022, 1), (key3009, 1), (key2757, 1), (key2752, 1), (key2752, -2), (key2922, -1), (key2918, -1), (key2918, 1), (key2657, 1), (key2919, 2), (key2919, -1), (key2659, -1), (key2724, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2827, 1), (key2807, 1), (key2807, -1), (key2614, -1), (key2858, -1), (key2792, -1), (key2858, 1), (key2638, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2801, -2), (key2801, 1), (key2608, 1), (key2851, 1), (key2698, 1), (key2851, -1), (key2624, -1)]

def rawRow248 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3025, 2), (key3007, 1), (key3009, 1), (key3016, -1), (key3025, -1), (key3007, -2), (key3011, 1), (key3021, 1), (key2918, 1), (key2919, 1), (key2922, -2), (key2657, -1), (key2659, -1), (key2757, 1), (key2922, 1), (key2657, 2), (key2752, -1), (key2918, -1), (key2784, -1), (key2792, -1), (key2827, 1), (key2868, 1), (key2630, 1), (key2638, 1), (key2724, -1), (key2868, -1), (key2614, -1), (key2630, -1), (key2669, 1), (key2784, 1), (key2778, 2), (key2801, -1), (key2851, -1), (key2624, -2), (key2698, 1), (key2851, 1), (key2608, 1), (key2624, 1), (key2663, -1), (key2698, -1)]

def rawRow249 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3025, 2), (key3009, 1), (key3007, 1), (key3025, -1), (key3016, -1), (key3007, -2), (key3021, 1), (key3011, 1), (key2919, 1), (key2918, 1), (key2922, -2), (key2659, -1), (key2657, -1), (key2922, 1), (key2757, 1), (key2657, 2), (key2918, -1), (key2752, -1), (key2792, -1), (key2784, -1), (key2868, 1), (key2827, 1), (key2638, 1), (key2630, 1), (key2868, -1), (key2724, -1), (key2630, -1), (key2614, -1), (key2784, 1), (key2669, 1), (key2778, 2), (key2851, -1), (key2801, -1), (key2624, -2), (key2851, 1), (key2698, 1), (key2624, 1), (key2608, 1), (key2698, -1), (key2663, -1)]

def rawRow250 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3022, 2), (key3011, 1), (key3016, 1), (key3009, -1), (key3022, -1), (key3011, -2), (key3007, 1), (key3021, 1), (key2918, 1), (key2922, 1), (key2919, -2), (key2752, -1), (key2757, -1), (key2659, 1), (key2919, 1), (key2752, 2), (key2657, -1), (key2918, -1), (key2807, -1), (key2827, -1), (key2792, 1), (key2858, 1), (key2704, 1), (key2724, 1), (key2638, -1), (key2858, -1), (key2669, -1), (key2704, -1), (key2614, 1), (key2807, 1), (key2801, 2), (key2778, -1), (key2851, -1), (key2698, -2), (key2624, 1), (key2851, 1), (key2663, 1), (key2698, 1), (key2608, -1), (key2801, -1)]

def rawRow251 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3022, 2), (key3016, 1), (key3011, 1), (key3022, -1), (key3009, -1), (key3011, -2), (key3021, 1), (key3007, 1), (key2922, 1), (key2918, 1), (key2919, -2), (key2757, -1), (key2752, -1), (key2919, 1), (key2659, 1), (key2752, 2), (key2918, -1), (key2657, -1), (key2827, -1), (key2807, -1), (key2858, 1), (key2792, 1), (key2724, 1), (key2704, 1), (key2858, -1), (key2638, -1), (key2704, -1), (key2669, -1), (key2807, 1), (key2614, 1), (key2801, 2), (key2851, -1), (key2778, -1), (key2698, -2), (key2851, 1), (key2624, 1), (key2698, 1), (key2663, 1), (key2801, -1), (key2608, -1)]

def rawRow252 : Integer.Sparse Key := [(key242, -1), (key242, -1), (key244, 2), (key254, 1), (key254, 1), (key265, -1), (key265, -1), (key269, -2), (key274, 1), (key274, 1), (key308, 1), (key308, 1), (key310, -2), (key322, -1), (key322, -1), (key333, 1), (key333, 1), (key337, 2), (key343, -1), (key343, -1), (key391, -1), (key391, -1), (key402, 1), (key402, 1), (key412, 1), (key412, 1), (key423, -1), (key423, -1), (key472, -1), (key472, -1), (key478, 1), (key478, 1), (key570, 2), (key575, -1), (key575, -1), (key580, -2), (key586, 1), (key586, 1), (key598, 1), (key598, 1), (key604, -1), (key604, -1)]

def rawRow255 : Integer.Sparse Key := [(key254, -1), (key254, -1), (key269, 2), (key242, 1), (key242, 1), (key274, -1), (key274, -1), (key244, -2), (key265, 1), (key265, 1), (key322, 1), (key322, 1), (key337, -2), (key308, -1), (key308, -1), (key343, 1), (key343, 1), (key310, 2), (key333, -1), (key333, -1), (key412, -1), (key412, -1), (key472, 1), (key472, 1), (key391, 1), (key391, 1), (key478, -1), (key478, -1), (key402, -1), (key402, -1), (key423, 1), (key423, 1), (key580, 2), (key598, -1), (key598, -1), (key570, -2), (key604, 1), (key604, 1), (key575, 1), (key575, 1), (key586, -1), (key586, -1)]

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

def rawRow2249 : Integer.Sparse Key := [(key1297, -1), (key1292, -1), (key1789, -1), (key1569, -1), (key1797, -1), (key1592, -1), (key1297, 2), (key1789, 2), (key1574, 2), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1), (key1338, -1), (key1317, -1), (key1773, -1), (key1547, -1), (key1814, -1), (key1656, -1), (key1325, -2), (key1816, -2), (key1623, -2), (key1344, 1), (key1325, 1), (key1779, 1), (key1555, 1), (key1816, 1), (key1658, 1)]

def rawRow2250 : Integer.Sparse Key := [(key1569, -1), (key1592, -1), (key1292, -1), (key1797, -1), (key1297, -1), (key1789, -1), (key1574, 2), (key1297, 2), (key1789, 2), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1), (key1547, -1), (key1656, -1), (key1317, -1), (key1814, -1), (key1338, -1), (key1773, -1), (key1623, -2), (key1325, -2), (key1816, -2), (key1555, 1), (key1658, 1), (key1325, 1), (key1816, 1), (key1344, 1), (key1779, 1)]

def rawRow2251 : Integer.Sparse Key := [(key1592, -1), (key1569, -1), (key1797, -1), (key1292, -1), (key1789, -1), (key1297, -1), (key1574, 2), (key1789, 2), (key1297, 2), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1), (key1656, -1), (key1547, -1), (key1814, -1), (key1317, -1), (key1773, -1), (key1338, -1), (key1623, -2), (key1816, -2), (key1325, -2), (key1658, 1), (key1555, 1), (key1816, 1), (key1325, 1), (key1779, 1), (key1344, 1)]

def rawRow2252 : Integer.Sparse Key := [(key1789, -1), (key1797, -1), (key1297, -1), (key1592, -1), (key1292, -1), (key1569, -1), (key1789, 2), (key1297, 2), (key1574, 2), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1), (key1773, -1), (key1814, -1), (key1338, -1), (key1656, -1), (key1317, -1), (key1547, -1), (key1816, -2), (key1325, -2), (key1623, -2), (key1779, 1), (key1816, 1), (key1344, 1), (key1658, 1), (key1325, 1), (key1555, 1)]

def rawRow2253 : Integer.Sparse Key := [(key1797, -1), (key1789, -1), (key1592, -1), (key1297, -1), (key1569, -1), (key1292, -1), (key1789, 2), (key1574, 2), (key1297, 2), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1), (key1814, -1), (key1773, -1), (key1656, -1), (key1338, -1), (key1547, -1), (key1317, -1), (key1816, -2), (key1623, -2), (key1325, -2), (key1816, 1), (key1779, 1), (key1658, 1), (key1344, 1), (key1555, 1), (key1325, 1)]

def rawRow2254 : Integer.Sparse Key := [(key1420, -1), (key1425, -1), (key1618, -1), (key1814, -1), (key1623, -1), (key1816, -1), (key1443, 2), (key1632, 2), (key1824, 2), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1), (key1443, -1), (key1465, -1), (key1592, -1), (key1797, -1), (key1666, -1), (key1824, -1), (key1392, -2), (key1547, -2), (key1773, -2), (key1425, 1), (key1456, 1), (key1574, 1), (key1789, 1), (key1656, 1), (key1814, 1)]

def rawRow2255 : Integer.Sparse Key := [(key1425, -1), (key1420, -1), (key1814, -1), (key1618, -1), (key1816, -1), (key1623, -1), (key1443, 2), (key1824, 2), (key1632, 2), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1), (key1465, -1), (key1443, -1), (key1797, -1), (key1592, -1), (key1824, -1), (key1666, -1), (key1392, -2), (key1773, -2), (key1547, -2), (key1456, 1), (key1425, 1), (key1789, 1), (key1574, 1), (key1814, 1), (key1656, 1)]

def rawRow2256 : Integer.Sparse Key := [(key1618, -1), (key1623, -1), (key1420, -1), (key1816, -1), (key1425, -1), (key1814, -1), (key1632, 2), (key1443, 2), (key1824, 2), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1), (key1592, -1), (key1666, -1), (key1443, -1), (key1824, -1), (key1465, -1), (key1797, -1), (key1547, -2), (key1392, -2), (key1773, -2), (key1574, 1), (key1656, 1), (key1425, 1), (key1814, 1), (key1456, 1), (key1789, 1)]

def rawRow2257 : Integer.Sparse Key := [(key1623, -1), (key1618, -1), (key1816, -1), (key1420, -1), (key1814, -1), (key1425, -1), (key1632, 2), (key1824, 2), (key1443, 2), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1), (key1666, -1), (key1592, -1), (key1824, -1), (key1443, -1), (key1797, -1), (key1465, -1), (key1547, -2), (key1773, -2), (key1392, -2), (key1656, 1), (key1574, 1), (key1814, 1), (key1425, 1), (key1789, 1), (key1456, 1)]

def rawRow2258 : Integer.Sparse Key := [(key1814, -1), (key1816, -1), (key1425, -1), (key1623, -1), (key1420, -1), (key1618, -1), (key1824, 2), (key1443, 2), (key1632, 2), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1), (key1797, -1), (key1824, -1), (key1465, -1), (key1666, -1), (key1443, -1), (key1592, -1), (key1773, -2), (key1392, -2), (key1547, -2), (key1789, 1), (key1814, 1), (key1456, 1), (key1656, 1), (key1425, 1), (key1574, 1)]

def rawRow2259 : Integer.Sparse Key := [(key1816, -1), (key1814, -1), (key1623, -1), (key1425, -1), (key1618, -1), (key1420, -1), (key1824, 2), (key1632, 2), (key1443, 2), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1), (key1824, -1), (key1797, -1), (key1666, -1), (key1465, -1), (key1592, -1), (key1443, -1), (key1773, -2), (key1547, -2), (key1392, -2), (key1814, 1), (key1789, 1), (key1656, 1), (key1456, 1), (key1574, 1), (key1425, 1)]

def rawRow2260 : Integer.Sparse Key := [(key1312, -1), (key1317, -1), (key1618, -1), (key1814, -1), (key1632, -1), (key1824, -1), (key1325, 2), (key1623, 2), (key1816, 2), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1), (key1325, -1), (key1344, -1), (key1555, -1), (key1779, -1), (key1658, -1), (key1816, -1), (key1297, -2), (key1574, -2), (key1789, -2), (key1317, 1), (key1338, 1), (key1547, 1), (key1773, 1), (key1656, 1), (key1814, 1)]

def rawRow2261 : Integer.Sparse Key := [(key1317, -1), (key1312, -1), (key1814, -1), (key1618, -1), (key1824, -1), (key1632, -1), (key1325, 2), (key1816, 2), (key1623, 2), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1), (key1344, -1), (key1325, -1), (key1779, -1), (key1555, -1), (key1816, -1), (key1658, -1), (key1297, -2), (key1789, -2), (key1574, -2), (key1338, 1), (key1317, 1), (key1773, 1), (key1547, 1), (key1814, 1), (key1656, 1)]

def rawRow2262 : Integer.Sparse Key := [(key1618, -1), (key1632, -1), (key1312, -1), (key1824, -1), (key1317, -1), (key1814, -1), (key1623, 2), (key1325, 2), (key1816, 2), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1), (key1555, -1), (key1658, -1), (key1325, -1), (key1816, -1), (key1344, -1), (key1779, -1), (key1574, -2), (key1297, -2), (key1789, -2), (key1547, 1), (key1656, 1), (key1317, 1), (key1814, 1), (key1338, 1), (key1773, 1)]

def rawRow2263 : Integer.Sparse Key := [(key1632, -1), (key1618, -1), (key1824, -1), (key1312, -1), (key1814, -1), (key1317, -1), (key1623, 2), (key1816, 2), (key1325, 2), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1), (key1658, -1), (key1555, -1), (key1816, -1), (key1325, -1), (key1779, -1), (key1344, -1), (key1574, -2), (key1789, -2), (key1297, -2), (key1656, 1), (key1547, 1), (key1814, 1), (key1317, 1), (key1773, 1), (key1338, 1)]

def rawRow2264 : Integer.Sparse Key := [(key1814, -1), (key1824, -1), (key1317, -1), (key1632, -1), (key1312, -1), (key1618, -1), (key1816, 2), (key1325, 2), (key1623, 2), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1), (key1779, -1), (key1816, -1), (key1344, -1), (key1658, -1), (key1325, -1), (key1555, -1), (key1789, -2), (key1297, -2), (key1574, -2), (key1773, 1), (key1814, 1), (key1338, 1), (key1656, 1), (key1317, 1), (key1547, 1)]

def rawRow2265 : Integer.Sparse Key := [(key1824, -1), (key1814, -1), (key1632, -1), (key1317, -1), (key1618, -1), (key1312, -1), (key1816, 2), (key1623, 2), (key1325, 2), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1), (key1816, -1), (key1779, -1), (key1658, -1), (key1344, -1), (key1555, -1), (key1325, -1), (key1789, -2), (key1574, -2), (key1297, -2), (key1814, 1), (key1773, 1), (key1656, 1), (key1338, 1), (key1547, 1), (key1317, 1)]

def rawRow2267 : Integer.Sparse Key := [(key3071, -2), (key3062, -2), (key3071, -2), (key3073, 2), (key3067, 2), (key3073, 2), (key3108, 2), (key3097, 2), (key3108, 2), (key3135, -6), (key3111, -2), (key3104, -2), (key3111, -2), (key3137, 6)]

def rawRow2268 : Integer.Sparse Key := [(key3071, -2), (key3071, -2), (key3062, -2), (key3073, 2), (key3073, 2), (key3067, 2), (key3108, 2), (key3108, 2), (key3097, 2), (key3135, -6), (key3111, -2), (key3111, -2), (key3104, -2), (key3137, 6)]

def rawRow2275 : Integer.Sparse Key := [(key3097, -2), (key3108, -2), (key3108, -2), (key3104, 2), (key3111, 2), (key3111, 2), (key3062, 2), (key3071, 2), (key3071, 2), (key3137, -6), (key3067, -2), (key3073, -2), (key3073, -2), (key3135, 6)]

def rawRow2276 : Integer.Sparse Key := [(key3108, -2), (key3097, -2), (key3108, -2), (key3111, 2), (key3104, 2), (key3111, 2), (key3071, 2), (key3062, 2), (key3071, 2), (key3137, -6), (key3073, -2), (key3067, -2), (key3073, -2), (key3135, 6)]

def rawRow2277 : Integer.Sparse Key := [(key3108, -2), (key3108, -2), (key3097, -2), (key3111, 2), (key3111, 2), (key3104, 2), (key3071, 2), (key3071, 2), (key3062, 2), (key3137, -6), (key3073, -2), (key3073, -2), (key3067, -2), (key3135, 6)]

def rawRow2296 : Integer.Sparse Key := [(key1292, -2), (key1297, -2), (key1297, -2), (key1312, 1), (key1317, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1338, 1), (key1387, 2), (key1392, 2), (key1392, 2), (key1542, -1), (key1547, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1773, -1), (key1420, -1), (key1425, -1), (key1420, -1), (key1456, -1), (key1425, -1), (key1456, -1), (key1569, 1), (key1574, 1), (key1569, 1), (key1789, 1), (key1574, 1), (key1789, 1)]

def rawRow2297 : Integer.Sparse Key := [(key1297, -2), (key1292, -2), (key1297, -2), (key1317, 1), (key1312, 1), (key1338, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1392, 2), (key1387, 2), (key1392, 2), (key1547, -1), (key1542, -1), (key1773, -1), (key1542, -1), (key1773, -1), (key1547, -1), (key1425, -1), (key1420, -1), (key1456, -1), (key1420, -1), (key1456, -1), (key1425, -1), (key1574, 1), (key1569, 1), (key1789, 1), (key1569, 1), (key1789, 1), (key1574, 1)]

def rawRow2298 : Integer.Sparse Key := [(key1297, -2), (key1297, -2), (key1292, -2), (key1338, 1), (key1338, 1), (key1317, 1), (key1317, 1), (key1312, 1), (key1312, 1), (key1392, 2), (key1392, 2), (key1387, 2), (key1773, -1), (key1773, -1), (key1547, -1), (key1547, -1), (key1542, -1), (key1542, -1), (key1456, -1), (key1456, -1), (key1425, -1), (key1425, -1), (key1420, -1), (key1420, -1), (key1789, 1), (key1789, 1), (key1574, 1), (key1574, 1), (key1569, 1), (key1569, 1)]

def rawRow2299 : Integer.Sparse Key := [(key1312, -2), (key1317, -2), (key1325, -2), (key1292, 1), (key1297, 1), (key1312, 1), (key1338, 1), (key1325, 1), (key1344, 1), (key1542, 2), (key1547, 2), (key1555, 2), (key1387, -1), (key1392, -1), (key1542, -1), (key1773, -1), (key1555, -1), (key1779, -1), (key1569, -1), (key1574, -1), (key1618, -1), (key1656, -1), (key1623, -1), (key1658, -1), (key1420, 1), (key1425, 1), (key1618, 1), (key1814, 1), (key1623, 1), (key1816, 1)]

def rawRow2300 : Integer.Sparse Key := [(key1317, -2), (key1312, -2), (key1325, -2), (key1297, 1), (key1292, 1), (key1338, 1), (key1312, 1), (key1344, 1), (key1325, 1), (key1547, 2), (key1542, 2), (key1555, 2), (key1392, -1), (key1387, -1), (key1773, -1), (key1542, -1), (key1779, -1), (key1555, -1), (key1574, -1), (key1569, -1), (key1656, -1), (key1618, -1), (key1658, -1), (key1623, -1), (key1425, 1), (key1420, 1), (key1814, 1), (key1618, 1), (key1816, 1), (key1623, 1)]

def rawRow2301 : Integer.Sparse Key := [(key1312, -2), (key1325, -2), (key1317, -2), (key1312, 1), (key1325, 1), (key1292, 1), (key1344, 1), (key1297, 1), (key1338, 1), (key1542, 2), (key1555, 2), (key1547, 2), (key1542, -1), (key1555, -1), (key1387, -1), (key1779, -1), (key1392, -1), (key1773, -1), (key1618, -1), (key1623, -1), (key1569, -1), (key1658, -1), (key1574, -1), (key1656, -1), (key1618, 1), (key1623, 1), (key1420, 1), (key1816, 1), (key1425, 1), (key1814, 1)]

def rawRow2302 : Integer.Sparse Key := [(key1325, -2), (key1312, -2), (key1317, -2), (key1325, 1), (key1312, 1), (key1344, 1), (key1292, 1), (key1338, 1), (key1297, 1), (key1555, 2), (key1542, 2), (key1547, 2), (key1555, -1), (key1542, -1), (key1779, -1), (key1387, -1), (key1773, -1), (key1392, -1), (key1623, -1), (key1618, -1), (key1658, -1), (key1569, -1), (key1656, -1), (key1574, -1), (key1623, 1), (key1618, 1), (key1816, 1), (key1420, 1), (key1814, 1), (key1425, 1)]

def rawRow2303 : Integer.Sparse Key := [(key1317, -2), (key1325, -2), (key1312, -2), (key1338, 1), (key1344, 1), (key1297, 1), (key1325, 1), (key1292, 1), (key1312, 1), (key1547, 2), (key1555, 2), (key1542, 2), (key1773, -1), (key1779, -1), (key1392, -1), (key1555, -1), (key1387, -1), (key1542, -1), (key1656, -1), (key1658, -1), (key1574, -1), (key1623, -1), (key1569, -1), (key1618, -1), (key1814, 1), (key1816, 1), (key1425, 1), (key1623, 1), (key1420, 1), (key1618, 1)]

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

def rawRow2304 : Integer.Sparse Key := [(key1325, -2), (key1317, -2), (key1312, -2), (key1344, 1), (key1338, 1), (key1325, 1), (key1297, 1), (key1312, 1), (key1292, 1), (key1555, 2), (key1547, 2), (key1542, 2), (key1779, -1), (key1773, -1), (key1555, -1), (key1392, -1), (key1542, -1), (key1387, -1), (key1658, -1), (key1656, -1), (key1623, -1), (key1574, -1), (key1618, -1), (key1569, -1), (key1816, 1), (key1814, 1), (key1623, 1), (key1425, 1), (key1618, 1), (key1420, 1)]

def rawRow2305 : Integer.Sparse Key := [(key1387, -2), (key1392, -2), (key1392, -2), (key1420, 1), (key1425, 1), (key1420, 1), (key1456, 1), (key1425, 1), (key1456, 1), (key1292, 2), (key1297, 2), (key1297, 2), (key1569, -1), (key1574, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1789, -1), (key1312, -1), (key1317, -1), (key1312, -1), (key1338, -1), (key1317, -1), (key1338, -1), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1)]

def rawRow2306 : Integer.Sparse Key := [(key1392, -2), (key1387, -2), (key1392, -2), (key1425, 1), (key1420, 1), (key1456, 1), (key1420, 1), (key1456, 1), (key1425, 1), (key1297, 2), (key1292, 2), (key1297, 2), (key1574, -1), (key1569, -1), (key1789, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1317, -1), (key1312, -1), (key1338, -1), (key1312, -1), (key1338, -1), (key1317, -1), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1)]

def rawRow2307 : Integer.Sparse Key := [(key1392, -2), (key1392, -2), (key1387, -2), (key1456, 1), (key1456, 1), (key1425, 1), (key1425, 1), (key1420, 1), (key1420, 1), (key1297, 2), (key1297, 2), (key1292, 2), (key1789, -1), (key1789, -1), (key1574, -1), (key1574, -1), (key1569, -1), (key1569, -1), (key1338, -1), (key1338, -1), (key1317, -1), (key1317, -1), (key1312, -1), (key1312, -1), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1)]

def rawRow2308 : Integer.Sparse Key := [(key1420, -2), (key1425, -2), (key1443, -2), (key1387, 1), (key1392, 1), (key1420, 1), (key1456, 1), (key1443, 1), (key1465, 1), (key1569, 2), (key1574, 2), (key1592, 2), (key1292, -1), (key1297, -1), (key1569, -1), (key1789, -1), (key1592, -1), (key1797, -1), (key1542, -1), (key1547, -1), (key1618, -1), (key1656, -1), (key1632, -1), (key1666, -1), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1)]

def rawRow2309 : Integer.Sparse Key := [(key1425, -2), (key1420, -2), (key1443, -2), (key1392, 1), (key1387, 1), (key1456, 1), (key1420, 1), (key1465, 1), (key1443, 1), (key1574, 2), (key1569, 2), (key1592, 2), (key1297, -1), (key1292, -1), (key1789, -1), (key1569, -1), (key1797, -1), (key1592, -1), (key1547, -1), (key1542, -1), (key1656, -1), (key1618, -1), (key1666, -1), (key1632, -1), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1)]

def rawRow2310 : Integer.Sparse Key := [(key1420, -2), (key1443, -2), (key1425, -2), (key1420, 1), (key1443, 1), (key1387, 1), (key1465, 1), (key1392, 1), (key1456, 1), (key1569, 2), (key1592, 2), (key1574, 2), (key1569, -1), (key1592, -1), (key1292, -1), (key1797, -1), (key1297, -1), (key1789, -1), (key1618, -1), (key1632, -1), (key1542, -1), (key1666, -1), (key1547, -1), (key1656, -1), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1)]

def rawRow2311 : Integer.Sparse Key := [(key1443, -2), (key1420, -2), (key1425, -2), (key1443, 1), (key1420, 1), (key1465, 1), (key1387, 1), (key1456, 1), (key1392, 1), (key1592, 2), (key1569, 2), (key1574, 2), (key1592, -1), (key1569, -1), (key1797, -1), (key1292, -1), (key1789, -1), (key1297, -1), (key1632, -1), (key1618, -1), (key1666, -1), (key1542, -1), (key1656, -1), (key1547, -1), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1)]

def rawRow2312 : Integer.Sparse Key := [(key1425, -2), (key1443, -2), (key1420, -2), (key1456, 1), (key1465, 1), (key1392, 1), (key1443, 1), (key1387, 1), (key1420, 1), (key1574, 2), (key1592, 2), (key1569, 2), (key1789, -1), (key1797, -1), (key1297, -1), (key1592, -1), (key1292, -1), (key1569, -1), (key1656, -1), (key1666, -1), (key1547, -1), (key1632, -1), (key1542, -1), (key1618, -1), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1)]

def rawRow2313 : Integer.Sparse Key := [(key1443, -2), (key1425, -2), (key1420, -2), (key1465, 1), (key1456, 1), (key1443, 1), (key1392, 1), (key1420, 1), (key1387, 1), (key1592, 2), (key1574, 2), (key1569, 2), (key1797, -1), (key1789, -1), (key1592, -1), (key1297, -1), (key1569, -1), (key1292, -1), (key1666, -1), (key1656, -1), (key1632, -1), (key1547, -1), (key1618, -1), (key1542, -1), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1)]

def rawRow2314 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, -2), (key1569, 1), (key1574, 1), (key1618, 1), (key1656, 1), (key1623, 1), (key1658, 1), (key1312, 2), (key1317, 2), (key1325, 2), (key1420, -1), (key1425, -1), (key1618, -1), (key1814, -1), (key1623, -1), (key1816, -1), (key1292, -1), (key1297, -1), (key1312, -1), (key1338, -1), (key1325, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1)]

def rawRow2315 : Integer.Sparse Key := [(key1547, -2), (key1542, -2), (key1555, -2), (key1574, 1), (key1569, 1), (key1656, 1), (key1618, 1), (key1658, 1), (key1623, 1), (key1317, 2), (key1312, 2), (key1325, 2), (key1425, -1), (key1420, -1), (key1814, -1), (key1618, -1), (key1816, -1), (key1623, -1), (key1297, -1), (key1292, -1), (key1338, -1), (key1312, -1), (key1344, -1), (key1325, -1), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1)]

def rawRow2316 : Integer.Sparse Key := [(key1542, -2), (key1555, -2), (key1547, -2), (key1618, 1), (key1623, 1), (key1569, 1), (key1658, 1), (key1574, 1), (key1656, 1), (key1312, 2), (key1325, 2), (key1317, 2), (key1618, -1), (key1623, -1), (key1420, -1), (key1816, -1), (key1425, -1), (key1814, -1), (key1312, -1), (key1325, -1), (key1292, -1), (key1344, -1), (key1297, -1), (key1338, -1), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1)]

def rawRow2317 : Integer.Sparse Key := [(key1555, -2), (key1542, -2), (key1547, -2), (key1623, 1), (key1618, 1), (key1658, 1), (key1569, 1), (key1656, 1), (key1574, 1), (key1325, 2), (key1312, 2), (key1317, 2), (key1623, -1), (key1618, -1), (key1816, -1), (key1420, -1), (key1814, -1), (key1425, -1), (key1325, -1), (key1312, -1), (key1344, -1), (key1292, -1), (key1338, -1), (key1297, -1), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1)]

def rawRow2318 : Integer.Sparse Key := [(key1547, -2), (key1555, -2), (key1542, -2), (key1656, 1), (key1658, 1), (key1574, 1), (key1623, 1), (key1569, 1), (key1618, 1), (key1317, 2), (key1325, 2), (key1312, 2), (key1814, -1), (key1816, -1), (key1425, -1), (key1623, -1), (key1420, -1), (key1618, -1), (key1338, -1), (key1344, -1), (key1297, -1), (key1325, -1), (key1292, -1), (key1312, -1), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1)]

def rawRow2319 : Integer.Sparse Key := [(key1555, -2), (key1547, -2), (key1542, -2), (key1658, 1), (key1656, 1), (key1623, 1), (key1574, 1), (key1618, 1), (key1569, 1), (key1325, 2), (key1317, 2), (key1312, 2), (key1816, -1), (key1814, -1), (key1623, -1), (key1425, -1), (key1618, -1), (key1420, -1), (key1344, -1), (key1338, -1), (key1325, -1), (key1297, -1), (key1312, -1), (key1292, -1), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1)]

def rawRow2320 : Integer.Sparse Key := [(key1569, -2), (key1574, -2), (key1592, -2), (key1542, 1), (key1547, 1), (key1618, 1), (key1656, 1), (key1632, 1), (key1666, 1), (key1420, 2), (key1425, 2), (key1443, 2), (key1312, -1), (key1317, -1), (key1618, -1), (key1814, -1), (key1632, -1), (key1824, -1), (key1387, -1), (key1392, -1), (key1420, -1), (key1456, -1), (key1443, -1), (key1465, -1), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1)]

def rawRow2321 : Integer.Sparse Key := [(key1574, -2), (key1569, -2), (key1592, -2), (key1547, 1), (key1542, 1), (key1656, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1425, 2), (key1420, 2), (key1443, 2), (key1317, -1), (key1312, -1), (key1814, -1), (key1618, -1), (key1824, -1), (key1632, -1), (key1392, -1), (key1387, -1), (key1456, -1), (key1420, -1), (key1465, -1), (key1443, -1), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1)]

def rawRow2322 : Integer.Sparse Key := [(key1569, -2), (key1592, -2), (key1574, -2), (key1618, 1), (key1632, 1), (key1542, 1), (key1666, 1), (key1547, 1), (key1656, 1), (key1420, 2), (key1443, 2), (key1425, 2), (key1618, -1), (key1632, -1), (key1312, -1), (key1824, -1), (key1317, -1), (key1814, -1), (key1420, -1), (key1443, -1), (key1387, -1), (key1465, -1), (key1392, -1), (key1456, -1), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1)]

def rawRow2323 : Integer.Sparse Key := [(key1592, -2), (key1569, -2), (key1574, -2), (key1632, 1), (key1618, 1), (key1666, 1), (key1542, 1), (key1656, 1), (key1547, 1), (key1443, 2), (key1420, 2), (key1425, 2), (key1632, -1), (key1618, -1), (key1824, -1), (key1312, -1), (key1814, -1), (key1317, -1), (key1443, -1), (key1420, -1), (key1465, -1), (key1387, -1), (key1456, -1), (key1392, -1), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1)]

def rawRow2324 : Integer.Sparse Key := [(key1574, -2), (key1592, -2), (key1569, -2), (key1656, 1), (key1666, 1), (key1547, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1425, 2), (key1443, 2), (key1420, 2), (key1814, -1), (key1824, -1), (key1317, -1), (key1632, -1), (key1312, -1), (key1618, -1), (key1456, -1), (key1465, -1), (key1392, -1), (key1443, -1), (key1387, -1), (key1420, -1), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1)]

def rawRow2325 : Integer.Sparse Key := [(key1592, -2), (key1574, -2), (key1569, -2), (key1666, 1), (key1656, 1), (key1632, 1), (key1547, 1), (key1618, 1), (key1542, 1), (key1443, 2), (key1425, 2), (key1420, 2), (key1824, -1), (key1814, -1), (key1632, -1), (key1317, -1), (key1618, -1), (key1312, -1), (key1465, -1), (key1456, -1), (key1443, -1), (key1392, -1), (key1420, -1), (key1387, -1), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1)]

def rawRow2326 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key997, -2), (key1012, 6), (key1028, 2), (key1032, 2), (key1032, 2), (key1120, -2), (key1120, -2), (key1196, -2), (key1068, -6), (key1147, 2), (key1147, 2), (key1209, 2)]

def rawRow2327 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key997, -2), (key1012, 6), (key1032, 2), (key1028, 2), (key1032, 2), (key1120, -2), (key1196, -2), (key1120, -2), (key1068, -6), (key1147, 2), (key1209, 2), (key1147, 2)]

def rawRow2328 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key993, -2), (key1012, 6), (key1032, 2), (key1032, 2), (key1028, 2), (key1196, -2), (key1120, -2), (key1120, -2), (key1068, -6), (key1209, 2), (key1147, 2), (key1147, 2)]

def rawRow2335 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1032, -2), (key1068, 6), (key993, 2), (key997, 2), (key997, 2), (key1147, -2), (key1147, -2), (key1209, -2), (key1012, -6), (key1120, 2), (key1120, 2), (key1196, 2)]

def rawRow2336 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1032, -2), (key1068, 6), (key997, 2), (key993, 2), (key997, 2), (key1147, -2), (key1209, -2), (key1147, -2), (key1012, -6), (key1120, 2), (key1196, 2), (key1120, 2)]

def rawRow2337 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1028, -2), (key1068, 6), (key997, 2), (key997, 2), (key993, 2), (key1209, -2), (key1147, -2), (key1147, -2), (key1012, -6), (key1196, 2), (key1120, 2), (key1120, 2)]

def rawRow2356 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2640, 1), (key2642, 1), (key2640, 1), (key2654, 1), (key2642, 1), (key2654, 1), (key2706, 2), (key2706, 2), (key2738, 2), (key2860, -1), (key2898, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2977, -1), (key2726, -1), (key2729, -1), (key2726, -1), (key2748, -1), (key2729, -1), (key2748, -1), (key2870, 1), (key2905, 1), (key2870, 1), (key2984, 1), (key2905, 1), (key2984, 1)]

def rawRow2357 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2642, 1), (key2640, 1), (key2654, 1), (key2640, 1), (key2654, 1), (key2642, 1), (key2706, 2), (key2738, 2), (key2706, 2), (key2898, -1), (key2860, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2729, -1), (key2726, -1), (key2748, -1), (key2726, -1), (key2748, -1), (key2729, -1), (key2905, 1), (key2870, 1), (key2984, 1), (key2870, 1), (key2984, 1), (key2905, 1)]

def rawRow2358 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2654, 1), (key2654, 1), (key2642, 1), (key2642, 1), (key2640, 1), (key2640, 1), (key2738, 2), (key2706, 2), (key2706, 2), (key2977, -1), (key2977, -1), (key2898, -1), (key2898, -1), (key2860, -1), (key2860, -1), (key2748, -1), (key2748, -1), (key2729, -1), (key2729, -1), (key2726, -1), (key2726, -1), (key2984, 1), (key2984, 1), (key2905, 1), (key2905, 1), (key2870, 1), (key2870, 1)]

def rawRow2359 : Integer.Sparse Key := [(key2616, -2), (key2640, -2), (key2654, -2), (key2616, 1), (key2619, 1), (key2632, 1), (key2649, 1), (key2642, 1), (key2654, 1), (key2809, 2), (key2860, 2), (key2898, 2), (key2706, -1), (key2738, -1), (key2809, -1), (key2951, -1), (key2898, -1), (key2977, -1), (key2829, -1), (key2832, -1), (key2870, -1), (key2905, -1), (key2883, -1), (key2913, -1), (key2726, 1), (key2748, 1), (key2829, 1), (key2961, 1), (key2913, 1), (key2992, 1)]

def rawRow2360 : Integer.Sparse Key := [(key2616, -2), (key2654, -2), (key2640, -2), (key2619, 1), (key2616, 1), (key2649, 1), (key2632, 1), (key2654, 1), (key2642, 1), (key2809, 2), (key2898, 2), (key2860, 2), (key2738, -1), (key2706, -1), (key2951, -1), (key2809, -1), (key2977, -1), (key2898, -1), (key2832, -1), (key2829, -1), (key2905, -1), (key2870, -1), (key2913, -1), (key2883, -1), (key2748, 1), (key2726, 1), (key2961, 1), (key2829, 1), (key2992, 1), (key2913, 1)]

def rawRow2361 : Integer.Sparse Key := [(key2640, -2), (key2616, -2), (key2654, -2), (key2632, 1), (key2642, 1), (key2616, 1), (key2654, 1), (key2619, 1), (key2649, 1), (key2860, 2), (key2809, 2), (key2898, 2), (key2809, -1), (key2898, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2870, -1), (key2883, -1), (key2829, -1), (key2913, -1), (key2832, -1), (key2905, -1), (key2829, 1), (key2913, 1), (key2726, 1), (key2992, 1), (key2748, 1), (key2961, 1)]

def rawRow2362 : Integer.Sparse Key := [(key2640, -2), (key2654, -2), (key2616, -2), (key2642, 1), (key2632, 1), (key2654, 1), (key2616, 1), (key2649, 1), (key2619, 1), (key2860, 2), (key2898, 2), (key2809, 2), (key2898, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2951, -1), (key2738, -1), (key2883, -1), (key2870, -1), (key2913, -1), (key2829, -1), (key2905, -1), (key2832, -1), (key2913, 1), (key2829, 1), (key2992, 1), (key2726, 1), (key2961, 1), (key2748, 1)]

def rawRow2363 : Integer.Sparse Key := [(key2654, -2), (key2616, -2), (key2640, -2), (key2649, 1), (key2654, 1), (key2619, 1), (key2642, 1), (key2616, 1), (key2632, 1), (key2898, 2), (key2809, 2), (key2860, 2), (key2951, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2706, -1), (key2809, -1), (key2905, -1), (key2913, -1), (key2832, -1), (key2883, -1), (key2829, -1), (key2870, -1), (key2961, 1), (key2992, 1), (key2748, 1), (key2913, 1), (key2726, 1), (key2829, 1)]

def rawRow2364 : Integer.Sparse Key := [(key2654, -2), (key2640, -2), (key2616, -2), (key2654, 1), (key2649, 1), (key2642, 1), (key2619, 1), (key2632, 1), (key2616, 1), (key2898, 2), (key2860, 2), (key2809, 2), (key2977, -1), (key2951, -1), (key2898, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2913, -1), (key2905, -1), (key2883, -1), (key2832, -1), (key2870, -1), (key2829, -1), (key2992, 1), (key2961, 1), (key2913, 1), (key2748, 1), (key2829, 1), (key2726, 1)]

def rawRow2365 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2726, 1), (key2729, 1), (key2726, 1), (key2748, 1), (key2729, 1), (key2748, 1), (key2632, 2), (key2632, 2), (key2649, 2), (key2870, -1), (key2905, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2984, -1), (key2640, -1), (key2642, -1), (key2640, -1), (key2654, -1), (key2642, -1), (key2654, -1), (key2860, 1), (key2898, 1), (key2860, 1), (key2977, 1), (key2898, 1), (key2977, 1)]

def rawRow2366 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2729, 1), (key2726, 1), (key2748, 1), (key2726, 1), (key2748, 1), (key2729, 1), (key2632, 2), (key2649, 2), (key2632, 2), (key2905, -1), (key2870, -1), (key2984, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2642, -1), (key2640, -1), (key2654, -1), (key2640, -1), (key2654, -1), (key2642, -1), (key2898, 1), (key2860, 1), (key2977, 1), (key2860, 1), (key2977, 1), (key2898, 1)]

def rawRow2367 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2748, 1), (key2748, 1), (key2729, 1), (key2729, 1), (key2726, 1), (key2726, 1), (key2649, 2), (key2632, 2), (key2632, 2), (key2984, -1), (key2984, -1), (key2905, -1), (key2905, -1), (key2870, -1), (key2870, -1), (key2654, -1), (key2654, -1), (key2642, -1), (key2642, -1), (key2640, -1), (key2640, -1), (key2977, 1), (key2977, 1), (key2898, 1), (key2898, 1), (key2860, 1), (key2860, 1)]

def rawRow2368 : Integer.Sparse Key := [(key2671, -2), (key2726, -2), (key2748, -2), (key2671, 1), (key2674, 1), (key2706, 1), (key2738, 1), (key2729, 1), (key2748, 1), (key2786, 2), (key2870, 2), (key2905, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2939, -1), (key2905, -1), (key2984, -1), (key2794, -1), (key2796, -1), (key2860, -1), (key2898, -1), (key2883, -1), (key2913, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2944, 1), (key2913, 1), (key2992, 1)]

def rawRow2369 : Integer.Sparse Key := [(key2671, -2), (key2748, -2), (key2726, -2), (key2674, 1), (key2671, 1), (key2738, 1), (key2706, 1), (key2748, 1), (key2729, 1), (key2786, 2), (key2905, 2), (key2870, 2), (key2649, -1), (key2632, -1), (key2939, -1), (key2786, -1), (key2984, -1), (key2905, -1), (key2796, -1), (key2794, -1), (key2898, -1), (key2860, -1), (key2913, -1), (key2883, -1), (key2654, 1), (key2640, 1), (key2944, 1), (key2794, 1), (key2992, 1), (key2913, 1)]

def rawRow2370 : Integer.Sparse Key := [(key2726, -2), (key2671, -2), (key2748, -2), (key2706, 1), (key2729, 1), (key2671, 1), (key2748, 1), (key2674, 1), (key2738, 1), (key2870, 2), (key2786, 2), (key2905, 2), (key2786, -1), (key2905, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2860, -1), (key2883, -1), (key2794, -1), (key2913, -1), (key2796, -1), (key2898, -1), (key2794, 1), (key2913, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2944, 1)]

def rawRow2371 : Integer.Sparse Key := [(key2726, -2), (key2748, -2), (key2671, -2), (key2729, 1), (key2706, 1), (key2748, 1), (key2671, 1), (key2738, 1), (key2674, 1), (key2870, 2), (key2905, 2), (key2786, 2), (key2905, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2939, -1), (key2649, -1), (key2883, -1), (key2860, -1), (key2913, -1), (key2794, -1), (key2898, -1), (key2796, -1), (key2913, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2944, 1), (key2654, 1)]

def rawRow2372 : Integer.Sparse Key := [(key2748, -2), (key2671, -2), (key2726, -2), (key2738, 1), (key2748, 1), (key2674, 1), (key2729, 1), (key2671, 1), (key2706, 1), (key2905, 2), (key2786, 2), (key2870, 2), (key2939, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2632, -1), (key2786, -1), (key2898, -1), (key2913, -1), (key2796, -1), (key2883, -1), (key2794, -1), (key2860, -1), (key2944, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2640, 1), (key2794, 1)]

def rawRow2373 : Integer.Sparse Key := [(key2748, -2), (key2726, -2), (key2671, -2), (key2748, 1), (key2738, 1), (key2729, 1), (key2674, 1), (key2706, 1), (key2671, 1), (key2905, 2), (key2870, 2), (key2786, 2), (key2984, -1), (key2939, -1), (key2905, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2913, -1), (key2898, -1), (key2883, -1), (key2796, -1), (key2860, -1), (key2794, -1), (key2992, 1), (key2944, 1), (key2913, 1), (key2654, 1), (key2794, 1), (key2640, 1)]

def rawRow2374 : Integer.Sparse Key := [(key2809, -2), (key2860, -2), (key2898, -2), (key2829, 1), (key2832, 1), (key2870, 1), (key2905, 1), (key2883, 1), (key2913, 1), (key2616, 2), (key2640, 2), (key2654, 2), (key2726, -1), (key2748, -1), (key2829, -1), (key2961, -1), (key2913, -1), (key2992, -1), (key2616, -1), (key2619, -1), (key2632, -1), (key2649, -1), (key2642, -1), (key2654, -1), (key2706, 1), (key2738, 1), (key2809, 1), (key2951, 1), (key2898, 1), (key2977, 1)]

def rawRow2375 : Integer.Sparse Key := [(key2809, -2), (key2898, -2), (key2860, -2), (key2832, 1), (key2829, 1), (key2905, 1), (key2870, 1), (key2913, 1), (key2883, 1), (key2616, 2), (key2654, 2), (key2640, 2), (key2748, -1), (key2726, -1), (key2961, -1), (key2829, -1), (key2992, -1), (key2913, -1), (key2619, -1), (key2616, -1), (key2649, -1), (key2632, -1), (key2654, -1), (key2642, -1), (key2738, 1), (key2706, 1), (key2951, 1), (key2809, 1), (key2977, 1), (key2898, 1)]

def rawRow2376 : Integer.Sparse Key := [(key2860, -2), (key2809, -2), (key2898, -2), (key2870, 1), (key2883, 1), (key2829, 1), (key2913, 1), (key2832, 1), (key2905, 1), (key2640, 2), (key2616, 2), (key2654, 2), (key2829, -1), (key2913, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2632, -1), (key2642, -1), (key2616, -1), (key2654, -1), (key2619, -1), (key2649, -1), (key2809, 1), (key2898, 1), (key2706, 1), (key2977, 1), (key2738, 1), (key2951, 1)]

def rawRow2377 : Integer.Sparse Key := [(key2860, -2), (key2898, -2), (key2809, -2), (key2883, 1), (key2870, 1), (key2913, 1), (key2829, 1), (key2905, 1), (key2832, 1), (key2640, 2), (key2654, 2), (key2616, 2), (key2913, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2961, -1), (key2748, -1), (key2642, -1), (key2632, -1), (key2654, -1), (key2616, -1), (key2649, -1), (key2619, -1), (key2898, 1), (key2809, 1), (key2977, 1), (key2706, 1), (key2951, 1), (key2738, 1)]

def rawRow2378 : Integer.Sparse Key := [(key2898, -2), (key2809, -2), (key2860, -2), (key2905, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2829, 1), (key2870, 1), (key2654, 2), (key2616, 2), (key2640, 2), (key2961, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2726, -1), (key2829, -1), (key2649, -1), (key2654, -1), (key2619, -1), (key2642, -1), (key2616, -1), (key2632, -1), (key2951, 1), (key2977, 1), (key2738, 1), (key2898, 1), (key2706, 1), (key2809, 1)]

def rawRow2379 : Integer.Sparse Key := [(key2898, -2), (key2860, -2), (key2809, -2), (key2913, 1), (key2905, 1), (key2883, 1), (key2832, 1), (key2870, 1), (key2829, 1), (key2654, 2), (key2640, 2), (key2616, 2), (key2992, -1), (key2961, -1), (key2913, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2654, -1), (key2649, -1), (key2642, -1), (key2619, -1), (key2632, -1), (key2616, -1), (key2977, 1), (key2951, 1), (key2898, 1), (key2738, 1), (key2809, 1), (key2706, 1)]

def rawRow2380 : Integer.Sparse Key := [(key2786, -2), (key2870, -2), (key2905, -2), (key2794, 1), (key2796, 1), (key2860, 1), (key2898, 1), (key2883, 1), (key2913, 1), (key2671, 2), (key2726, 2), (key2748, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2944, -1), (key2913, -1), (key2992, -1), (key2671, -1), (key2674, -1), (key2706, -1), (key2738, -1), (key2729, -1), (key2748, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2939, 1), (key2905, 1), (key2984, 1)]

def rawRow2381 : Integer.Sparse Key := [(key2786, -2), (key2905, -2), (key2870, -2), (key2796, 1), (key2794, 1), (key2898, 1), (key2860, 1), (key2913, 1), (key2883, 1), (key2671, 2), (key2748, 2), (key2726, 2), (key2654, -1), (key2640, -1), (key2944, -1), (key2794, -1), (key2992, -1), (key2913, -1), (key2674, -1), (key2671, -1), (key2738, -1), (key2706, -1), (key2748, -1), (key2729, -1), (key2649, 1), (key2632, 1), (key2939, 1), (key2786, 1), (key2984, 1), (key2905, 1)]

def rawRow2382 : Integer.Sparse Key := [(key2870, -2), (key2786, -2), (key2905, -2), (key2860, 1), (key2883, 1), (key2794, 1), (key2913, 1), (key2796, 1), (key2898, 1), (key2726, 2), (key2671, 2), (key2748, 2), (key2794, -1), (key2913, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2706, -1), (key2729, -1), (key2671, -1), (key2748, -1), (key2674, -1), (key2738, -1), (key2786, 1), (key2905, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2939, 1)]

def rawRow2383 : Integer.Sparse Key := [(key2870, -2), (key2905, -2), (key2786, -2), (key2883, 1), (key2860, 1), (key2913, 1), (key2794, 1), (key2898, 1), (key2796, 1), (key2726, 2), (key2748, 2), (key2671, 2), (key2913, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2944, -1), (key2654, -1), (key2729, -1), (key2706, -1), (key2748, -1), (key2671, -1), (key2738, -1), (key2674, -1), (key2905, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2939, 1), (key2649, 1)]

def rawRow2384 : Integer.Sparse Key := [(key2905, -2), (key2786, -2), (key2870, -2), (key2898, 1), (key2913, 1), (key2796, 1), (key2883, 1), (key2794, 1), (key2860, 1), (key2748, 2), (key2671, 2), (key2726, 2), (key2944, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2640, -1), (key2794, -1), (key2738, -1), (key2748, -1), (key2674, -1), (key2729, -1), (key2671, -1), (key2706, -1), (key2939, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2632, 1), (key2786, 1)]

def rawRow2385 : Integer.Sparse Key := [(key2905, -2), (key2870, -2), (key2786, -2), (key2913, 1), (key2898, 1), (key2883, 1), (key2796, 1), (key2860, 1), (key2794, 1), (key2748, 2), (key2726, 2), (key2671, 2), (key2992, -1), (key2944, -1), (key2913, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2748, -1), (key2738, -1), (key2729, -1), (key2674, -1), (key2706, -1), (key2671, -1), (key2984, 1), (key2939, 1), (key2905, 1), (key2649, 1), (key2786, 1), (key2632, 1)]

def rawRow2386 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2375, -2), (key2387, 6), (key2399, 2), (key2403, 2), (key2403, 2), (key2477, -2), (key2477, -2), (key2541, -2), (key2434, -6), (key2500, 2), (key2500, 2), (key2552, 2)]

def rawRow2387 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2375, -2), (key2387, 6), (key2403, 2), (key2399, 2), (key2403, 2), (key2477, -2), (key2541, -2), (key2477, -2), (key2434, -6), (key2500, 2), (key2552, 2), (key2500, 2)]

def rawRow2388 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2371, -2), (key2387, 6), (key2403, 2), (key2403, 2), (key2399, 2), (key2541, -2), (key2477, -2), (key2477, -2), (key2434, -6), (key2552, 2), (key2500, 2), (key2500, 2)]

def rawRow2395 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2403, -2), (key2434, 6), (key2371, 2), (key2375, 2), (key2375, 2), (key2500, -2), (key2500, -2), (key2552, -2), (key2387, -6), (key2477, 2), (key2477, 2), (key2541, 2)]

def rawRow2396 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2403, -2), (key2434, 6), (key2375, 2), (key2371, 2), (key2375, 2), (key2500, -2), (key2552, -2), (key2500, -2), (key2387, -6), (key2477, 2), (key2541, 2), (key2477, 2)]

def rawRow2397 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2399, -2), (key2434, 6), (key2375, 2), (key2375, 2), (key2371, 2), (key2552, -2), (key2500, -2), (key2500, -2), (key2387, -6), (key2541, 2), (key2477, 2), (key2477, 2)]

def rawRow2416 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2373, -2), (key2386, 6), (key2762, 2), (key2765, 2), (key2765, 2), (key2886, -2), (key2886, -2), (key2908, -2), (key2928, -6), (key2965, 2), (key2965, 2), (key2987, 2)]

def rawRow2417 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2373, -2), (key2386, 6), (key2765, 2), (key2762, 2), (key2765, 2), (key2886, -2), (key2908, -2), (key2886, -2), (key2928, -6), (key2965, 2), (key2987, 2), (key2965, 2)]

def rawRow2418 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2370, -2), (key2386, 6), (key2765, 2), (key2765, 2), (key2762, 2), (key2908, -2), (key2886, -2), (key2886, -2), (key2928, -6), (key2987, 2), (key2965, 2), (key2965, 2)]

def rawRow2425 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2401, -2), (key2433, 6), (key2583, 2), (key2586, 2), (key2586, 2), (key2965, -2), (key2965, -2), (key2987, -2), (key2597, -6), (key2886, 2), (key2886, 2), (key2908, 2)]

def rawRow2426 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2401, -2), (key2433, 6), (key2586, 2), (key2583, 2), (key2586, 2), (key2965, -2), (key2987, -2), (key2965, -2), (key2597, -6), (key2886, 2), (key2908, 2), (key2886, 2)]

def rawRow2427 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2398, -2), (key2433, 6), (key2586, 2), (key2586, 2), (key2583, 2), (key2987, -2), (key2965, -2), (key2965, -2), (key2597, -6), (key2908, 2), (key2886, 2), (key2886, 2)]

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

def rawRow2446 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2663, 2), (key2666, 2), (key2666, 2), (key2698, -1), (key2701, -1), (key2698, -1), (key2722, -1), (key2701, -1), (key2722, -1), (key2778, -1), (key2781, -1), (key2778, -1), (key2790, -1), (key2781, -1), (key2790, -1), (key2801, 1), (key2804, 1), (key2801, 1), (key2825, 1), (key2804, 1), (key2825, 1)]

def rawRow2447 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2666, 2), (key2663, 2), (key2666, 2), (key2701, -1), (key2698, -1), (key2722, -1), (key2698, -1), (key2722, -1), (key2701, -1), (key2781, -1), (key2778, -1), (key2790, -1), (key2778, -1), (key2790, -1), (key2781, -1), (key2804, 1), (key2801, 1), (key2825, 1), (key2801, 1), (key2825, 1), (key2804, 1)]

def rawRow2448 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2666, 2), (key2666, 2), (key2663, 2), (key2722, -1), (key2722, -1), (key2701, -1), (key2701, -1), (key2698, -1), (key2698, -1), (key2790, -1), (key2790, -1), (key2781, -1), (key2781, -1), (key2778, -1), (key2778, -1), (key2825, 1), (key2825, 1), (key2804, 1), (key2804, 1), (key2801, 1), (key2801, 1)]

def rawRow2449 : Integer.Sparse Key := [(key2624, -2), (key2627, -2), (key2636, -2), (key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2698, 2), (key2701, 2), (key2734, 2), (key2663, -1), (key2666, -1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, -1), (key2851, -1), (key2856, -1), (key2892, -1), (key2895, -1), (key2778, 1), (key2781, 1), (key2851, 1), (key2866, 1), (key2892, 1), (key2902, 1)]

def rawRow2450 : Integer.Sparse Key := [(key2627, -2), (key2624, -2), (key2636, -2), (key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2701, 2), (key2698, 2), (key2734, 2), (key2666, -1), (key2663, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2734, -1), (key2804, -1), (key2801, -1), (key2856, -1), (key2851, -1), (key2895, -1), (key2892, -1), (key2781, 1), (key2778, 1), (key2866, 1), (key2851, 1), (key2902, 1), (key2892, 1)]

def rawRow2451 : Integer.Sparse Key := [(key2624, -2), (key2636, -2), (key2627, -2), (key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 2), (key2734, 2), (key2701, 2), (key2698, -1), (key2734, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2851, -1), (key2892, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2851, 1), (key2892, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2866, 1)]

def rawRow2452 : Integer.Sparse Key := [(key2636, -2), (key2624, -2), (key2627, -2), (key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 2), (key2698, 2), (key2701, 2), (key2734, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2722, -1), (key2666, -1), (key2892, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2856, -1), (key2804, -1), (key2892, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2866, 1), (key2781, 1)]

def rawRow2453 : Integer.Sparse Key := [(key2627, -2), (key2636, -2), (key2624, -2), (key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2701, 2), (key2734, 2), (key2698, 2), (key2722, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2663, -1), (key2698, -1), (key2856, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2801, -1), (key2851, -1), (key2866, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2778, 1), (key2851, 1)]

def rawRow2454 : Integer.Sparse Key := [(key2636, -2), (key2627, -2), (key2624, -2), (key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2734, 2), (key2701, 2), (key2698, 2), (key2745, -1), (key2722, -1), (key2734, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2895, -1), (key2856, -1), (key2892, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 1), (key2866, 1), (key2892, 1), (key2781, 1), (key2851, 1), (key2778, 1)]

def rawRow2455 : Integer.Sparse Key := [(key2663, -2), (key2666, -2), (key2666, -2), (key2698, 1), (key2701, 1), (key2698, 1), (key2734, 1), (key2701, 1), (key2734, 1), (key2608, 2), (key2611, 2), (key2611, 2), (key2801, -1), (key2804, -1), (key2801, -1), (key2825, -1), (key2804, -1), (key2825, -1), (key2624, -1), (key2627, -1), (key2624, -1), (key2636, -1), (key2627, -1), (key2636, -1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1)]

def rawRow2456 : Integer.Sparse Key := [(key2666, -2), (key2663, -2), (key2666, -2), (key2701, 1), (key2698, 1), (key2734, 1), (key2698, 1), (key2734, 1), (key2701, 1), (key2611, 2), (key2608, 2), (key2611, 2), (key2804, -1), (key2801, -1), (key2825, -1), (key2801, -1), (key2825, -1), (key2804, -1), (key2627, -1), (key2624, -1), (key2636, -1), (key2624, -1), (key2636, -1), (key2627, -1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1)]

def rawRow2457 : Integer.Sparse Key := [(key2666, -2), (key2666, -2), (key2663, -2), (key2734, 1), (key2734, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2611, 2), (key2611, 2), (key2608, 2), (key2825, -1), (key2825, -1), (key2804, -1), (key2804, -1), (key2801, -1), (key2801, -1), (key2636, -1), (key2636, -1), (key2627, -1), (key2627, -1), (key2624, -1), (key2624, -1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1)]

def rawRow2458 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2801, 2), (key2804, 2), (key2825, 2), (key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2698, -1), (key2701, -1), (key2851, -1), (key2856, -1), (key2971, -1), (key2974, -1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1)]

def rawRow2459 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2804, 2), (key2801, 2), (key2825, 2), (key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2701, -1), (key2698, -1), (key2856, -1), (key2851, -1), (key2974, -1), (key2971, -1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1)]

def rawRow2460 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 2), (key2825, 2), (key2804, 2), (key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2851, -1), (key2971, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1)]

def rawRow2461 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 2), (key2801, 2), (key2804, 2), (key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2856, -1), (key2701, -1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1)]

def rawRow2462 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2804, 2), (key2825, 2), (key2801, 2), (key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2856, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2698, -1), (key2851, -1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1)]

def rawRow2463 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2825, 2), (key2804, 2), (key2801, 2), (key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2974, -1), (key2856, -1), (key2971, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1)]

def rawRow2464 : Integer.Sparse Key := [(key2778, -2), (key2781, -2), (key2790, -2), (key2801, 1), (key2804, 1), (key2851, 1), (key2892, 1), (key2856, 1), (key2895, 1), (key2624, 2), (key2627, 2), (key2636, 2), (key2698, -1), (key2701, -1), (key2851, -1), (key2971, -1), (key2856, -1), (key2974, -1), (key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1)]

def rawRow2465 : Integer.Sparse Key := [(key2781, -2), (key2778, -2), (key2790, -2), (key2804, 1), (key2801, 1), (key2892, 1), (key2851, 1), (key2895, 1), (key2856, 1), (key2627, 2), (key2624, 2), (key2636, 2), (key2701, -1), (key2698, -1), (key2971, -1), (key2851, -1), (key2974, -1), (key2856, -1), (key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1)]

def rawRow2466 : Integer.Sparse Key := [(key2778, -2), (key2790, -2), (key2781, -2), (key2851, 1), (key2856, 1), (key2801, 1), (key2895, 1), (key2804, 1), (key2892, 1), (key2624, 2), (key2636, 2), (key2627, 2), (key2851, -1), (key2856, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1)]

def rawRow2467 : Integer.Sparse Key := [(key2790, -2), (key2778, -2), (key2781, -2), (key2856, 1), (key2851, 1), (key2895, 1), (key2801, 1), (key2892, 1), (key2804, 1), (key2636, 2), (key2624, 2), (key2627, 2), (key2856, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2971, -1), (key2701, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1)]

def rawRow2468 : Integer.Sparse Key := [(key2781, -2), (key2790, -2), (key2778, -2), (key2892, 1), (key2895, 1), (key2804, 1), (key2856, 1), (key2801, 1), (key2851, 1), (key2627, 2), (key2636, 2), (key2624, 2), (key2971, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2698, -1), (key2851, -1), (key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1)]

def rawRow2469 : Integer.Sparse Key := [(key2790, -2), (key2781, -2), (key2778, -2), (key2895, 1), (key2892, 1), (key2856, 1), (key2804, 1), (key2851, 1), (key2801, 1), (key2636, 2), (key2627, 2), (key2624, 2), (key2974, -1), (key2971, -1), (key2856, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1)]

def rawRow2470 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2778, 1), (key2781, 1), (key2851, 1), (key2892, 1), (key2866, 1), (key2902, 1), (key2698, 2), (key2701, 2), (key2722, 2), (key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1)]

def rawRow2471 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2781, 1), (key2778, 1), (key2892, 1), (key2851, 1), (key2902, 1), (key2866, 1), (key2701, 2), (key2698, 2), (key2722, 2), (key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1)]

def rawRow2472 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2851, 1), (key2866, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2698, 2), (key2722, 2), (key2701, 2), (key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1)]

def rawRow2473 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2866, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2892, 1), (key2781, 1), (key2722, 2), (key2698, 2), (key2701, 2), (key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1)]

def rawRow2474 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2892, 1), (key2902, 1), (key2781, 1), (key2866, 1), (key2778, 1), (key2851, 1), (key2701, 2), (key2722, 2), (key2698, 2), (key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1)]

def rawRow2475 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2902, 1), (key2892, 1), (key2866, 1), (key2781, 1), (key2851, 1), (key2778, 1), (key2722, 2), (key2701, 2), (key2698, 2), (key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1)]

def rawRow2479 : Integer.Sparse Key := [(key2179, -2), (key2179, -2), (key2179, -2), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2175, 1), (key2281, 2), (key2281, 2), (key2281, 2), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2330, -1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1)]

def rawRow2486 : Integer.Sparse Key := [(key2281, -2), (key2281, -2), (key2281, -2), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2330, 1), (key2179, 2), (key2179, 2), (key2179, 2), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2175, -1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1)]

def rawRow2493 : Integer.Sparse Key := [(key755, -6), (key754, 2), (key754, 2), (key754, 2), (key844, 6), (key843, -2), (key843, -2), (key843, -2), (key945, -2), (key945, -2), (key945, -2), (key944, 2), (key944, 2), (key944, 2)]

def rawRow2500 : Integer.Sparse Key := [(key844, -6), (key945, 2), (key945, 2), (key945, 2), (key755, 6), (key944, -2), (key944, -2), (key944, -2), (key754, -2), (key754, -2), (key754, -2), (key843, 2), (key843, 2), (key843, 2)]

def rawRow2507 : Integer.Sparse Key := [(key2085, -2), (key2085, -2), (key2085, -2), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2079, 1), (key2187, 2), (key2187, 2), (key2187, 2), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2176, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2287, -1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1)]

def rawRow2514 : Integer.Sparse Key := [(key2187, -2), (key2187, -2), (key2187, -2), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2085, 2), (key2085, 2), (key2085, 2), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2279, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2079, -1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1), (key2176, 1)]

def rawRow2521 : Integer.Sparse Key := [(key715, -2), (key715, -2), (key715, -2), (key713, 6), (key914, 2), (key914, 2), (key914, 2), (key890, -2), (key890, -2), (key890, -2), (key966, -6), (key959, 2), (key959, 2), (key959, 2)]

def rawRow2528 : Integer.Sparse Key := [(key914, -2), (key914, -2), (key914, -2), (key966, 6), (key715, 2), (key715, 2), (key715, 2), (key959, -2), (key959, -2), (key959, -2), (key713, -6), (key890, 2), (key890, 2), (key890, 2)]

def rawRow2535 : Integer.Sparse Key := [(key2099, -6), (key2098, 2), (key2098, 2), (key2098, 2), (key2206, 6), (key2203, -2), (key2203, -2), (key2203, -2), (key2321, -2), (key2321, -2), (key2321, -2), (key2318, 2), (key2318, 2), (key2318, 2)]

def rawRow2542 : Integer.Sparse Key := [(key2206, -6), (key2321, 2), (key2321, 2), (key2321, 2), (key2099, 6), (key2318, -2), (key2318, -2), (key2318, -2), (key2098, -2), (key2098, -2), (key2098, -2), (key2203, 2), (key2203, 2), (key2203, 2)]

def rawRow2549 : Integer.Sparse Key := [(key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key817, 2), (key817, 2), (key817, 2), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key897, -1), (key962, -2), (key962, -2), (key962, -2), (key960, 1), (key960, 1), (key960, 1), (key960, 1), (key960, 1), (key960, 1)]

def rawRow2556 : Integer.Sparse Key := [(key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key962, 2), (key962, 2), (key962, 2), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key960, -1), (key817, -2), (key817, -2), (key817, -2), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1)]

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

def rawRow2563 : Integer.Sparse Key := [(key2183, -2), (key2183, -2), (key2183, -2), (key2182, 2), (key2182, 2), (key2182, 2), (key2285, 2), (key2285, 2), (key2285, 2), (key2284, -6), (key2346, -2), (key2346, -2), (key2346, -2), (key2345, 6)]

def rawRow2570 : Integer.Sparse Key := [(key2285, -2), (key2285, -2), (key2285, -2), (key2346, 2), (key2346, 2), (key2346, 2), (key2183, 2), (key2183, 2), (key2183, 2), (key2345, -6), (key2182, -2), (key2182, -2), (key2182, -2), (key2284, 6)]

def rawRow2577 : Integer.Sparse Key := [(key743, -2), (key743, -2), (key743, -2), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key738, 1), (key825, 2), (key825, 2), (key825, 2), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key818, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key908, -1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1)]

def rawRow2584 : Integer.Sparse Key := [(key825, -2), (key825, -2), (key825, -2), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key743, 2), (key743, 2), (key743, 2), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key902, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key738, -1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1), (key818, 1)]

def rawRow2591 : Integer.Sparse Key := [(key722, -2), (key722, -2), (key722, -2), (key721, 6), (key939, 2), (key939, 2), (key939, 2), (key921, -2), (key921, -2), (key921, -2), (key966, -6), (key959, 2), (key959, 2), (key959, 2)]

def rawRow2598 : Integer.Sparse Key := [(key939, -2), (key939, -2), (key939, -2), (key966, 6), (key722, 2), (key722, 2), (key722, 2), (key959, -2), (key959, -2), (key959, -2), (key721, -6), (key921, 2), (key921, 2), (key921, 2)]

def rawRow2605 : Integer.Sparse Key := [(key2082, -2), (key2082, -2), (key2082, -2), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2078, 1), (key2289, 2), (key2289, 2), (key2289, 2), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2275, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2333, -1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1), (key2328, 1)]

def rawRow2612 : Integer.Sparse Key := [(key2289, -2), (key2289, -2), (key2289, -2), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2333, 1), (key2082, 2), (key2082, 2), (key2082, 2), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2328, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2078, -1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1), (key2275, 1)]

def rawRow2619 : Integer.Sparse Key := [(key2000, -2), (key2000, -2), (key2000, -2), (key1998, 6), (key2292, 2), (key2292, 2), (key2292, 2), (key2267, -2), (key2267, -2), (key2267, -2), (key2349, -6), (key2340, 2), (key2340, 2), (key2340, 2)]

def rawRow2626 : Integer.Sparse Key := [(key2292, -2), (key2292, -2), (key2292, -2), (key2349, 6), (key2000, 2), (key2000, 2), (key2000, 2), (key2340, -2), (key2340, -2), (key2340, -2), (key1998, -6), (key2267, 2), (key2267, 2), (key2267, 2)]

def rawRow2633 : Integer.Sparse Key := [(key2007, -2), (key2007, -2), (key2007, -2), (key2006, 6), (key2313, 2), (key2313, 2), (key2313, 2), (key2299, -2), (key2299, -2), (key2299, -2), (key2349, -6), (key2340, 2), (key2340, 2), (key2340, 2)]

def rawRow2640 : Integer.Sparse Key := [(key2313, -2), (key2313, -2), (key2313, -2), (key2349, 6), (key2007, 2), (key2007, 2), (key2007, 2), (key2340, -2), (key2340, -2), (key2340, -2), (key2006, -6), (key2299, 2), (key2299, 2), (key2299, 2)]

def rawRow2647 : Integer.Sparse Key := [(key2095, -2), (key2095, -2), (key2095, -2), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2092, 1), (key2200, 2), (key2200, 2), (key2200, 2), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2194, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2310, -1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1), (key2305, 1)]

def rawRow2654 : Integer.Sparse Key := [(key2200, -2), (key2200, -2), (key2200, -2), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2310, 1), (key2095, 2), (key2095, 2), (key2095, 2), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2305, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2092, -1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1), (key2194, 1)]

def rawRow2661 : Integer.Sparse Key := [(key778, -2), (key778, -2), (key778, -2), (key776, 6), (key811, 2), (key811, 2), (key811, 2), (key801, -2), (key801, -2), (key801, -2), (key839, -6), (key836, 2), (key836, 2), (key836, 2)]

def rawRow2668 : Integer.Sparse Key := [(key836, -2), (key836, -2), (key836, -2), (key839, 6), (key778, 2), (key778, 2), (key778, 2), (key811, -2), (key811, -2), (key811, -2), (key776, -6), (key801, 2), (key801, 2), (key801, 2)]

def rawRow2672 : Integer.Sparse Key := [(key2407, -2), (key2441, -2), (key2441, -2), (key2410, 1), (key2410, 1), (key2441, 1), (key2441, 1), (key2445, 1), (key2445, 1), (key2473, 2), (key2507, 2), (key2507, 2), (key2483, -1), (key2483, -1), (key2507, -1), (key2507, -1), (key2526, -1), (key2526, -1), (key2539, -1), (key2539, -1), (key2555, -1), (key2555, -1), (key2557, -1), (key2557, -1), (key2544, 1), (key2544, 1), (key2555, 1), (key2555, 1), (key2565, 1), (key2565, 1)]

def rawRow2673 : Integer.Sparse Key := [(key2441, -2), (key2407, -2), (key2441, -2), (key2441, 1), (key2445, 1), (key2410, 1), (key2445, 1), (key2410, 1), (key2441, 1), (key2507, 2), (key2473, 2), (key2507, 2), (key2507, -1), (key2526, -1), (key2483, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2555, -1), (key2557, -1), (key2539, -1), (key2557, -1), (key2539, -1), (key2555, -1), (key2555, 1), (key2565, 1), (key2544, 1), (key2565, 1), (key2544, 1), (key2555, 1)]

def rawRow2674 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2407, -2), (key2445, 1), (key2441, 1), (key2445, 1), (key2410, 1), (key2441, 1), (key2410, 1), (key2507, 2), (key2507, 2), (key2473, 2), (key2526, -1), (key2507, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2483, -1), (key2557, -1), (key2555, -1), (key2557, -1), (key2539, -1), (key2555, -1), (key2539, -1), (key2565, 1), (key2555, 1), (key2565, 1), (key2544, 1), (key2555, 1), (key2544, 1)]

def rawRow2675 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2445, -2), (key2407, 1), (key2410, 1), (key2407, 1), (key2441, 1), (key2410, 1), (key2441, 1), (key2483, 2), (key2483, 2), (key2526, 2), (key2473, -1), (key2483, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2507, -1), (key2544, -1), (key2545, -1), (key2544, -1), (key2565, -1), (key2545, -1), (key2565, -1), (key2539, 1), (key2545, 1), (key2539, 1), (key2557, 1), (key2545, 1), (key2557, 1)]

def rawRow2676 : Integer.Sparse Key := [(key2410, -2), (key2445, -2), (key2410, -2), (key2410, 1), (key2407, 1), (key2441, 1), (key2407, 1), (key2441, 1), (key2410, 1), (key2483, 2), (key2526, 2), (key2483, 2), (key2483, -1), (key2473, -1), (key2507, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2545, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2545, -1), (key2545, 1), (key2539, 1), (key2557, 1), (key2539, 1), (key2557, 1), (key2545, 1)]

def rawRow2677 : Integer.Sparse Key := [(key2445, -2), (key2410, -2), (key2410, -2), (key2441, 1), (key2441, 1), (key2410, 1), (key2410, 1), (key2407, 1), (key2407, 1), (key2526, 2), (key2483, 2), (key2483, 2), (key2507, -1), (key2507, -1), (key2483, -1), (key2483, -1), (key2473, -1), (key2473, -1), (key2565, -1), (key2565, -1), (key2545, -1), (key2545, -1), (key2544, -1), (key2544, -1), (key2557, 1), (key2557, 1), (key2545, 1), (key2545, 1), (key2539, 1), (key2539, 1)]

def rawRow2678 : Integer.Sparse Key := [(key2848, -2), (key2970, -2), (key2970, -2), (key2882, 1), (key2882, 1), (key2991, 1), (key2991, 1), (key2993, 1), (key2993, 1), (key2407, 2), (key2441, 2), (key2441, 2), (key2544, -1), (key2544, -1), (key2555, -1), (key2555, -1), (key2565, -1), (key2565, -1), (key2410, -1), (key2410, -1), (key2441, -1), (key2441, -1), (key2445, -1), (key2445, -1), (key2483, 1), (key2483, 1), (key2507, 1), (key2507, 1), (key2526, 1), (key2526, 1)]

def rawRow2679 : Integer.Sparse Key := [(key2970, -2), (key2848, -2), (key2970, -2), (key2991, 1), (key2993, 1), (key2882, 1), (key2993, 1), (key2882, 1), (key2991, 1), (key2441, 2), (key2407, 2), (key2441, 2), (key2555, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2441, -1), (key2445, -1), (key2410, -1), (key2445, -1), (key2410, -1), (key2441, -1), (key2507, 1), (key2526, 1), (key2483, 1), (key2526, 1), (key2483, 1), (key2507, 1)]

def rawRow2680 : Integer.Sparse Key := [(key2970, -2), (key2970, -2), (key2848, -2), (key2993, 1), (key2991, 1), (key2993, 1), (key2882, 1), (key2991, 1), (key2882, 1), (key2441, 2), (key2441, 2), (key2407, 2), (key2565, -1), (key2555, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2544, -1), (key2445, -1), (key2441, -1), (key2445, -1), (key2410, -1), (key2441, -1), (key2410, -1), (key2526, 1), (key2507, 1), (key2526, 1), (key2483, 1), (key2507, 1), (key2483, 1)]

def rawRow2681 : Integer.Sparse Key := [(key2595, -2), (key2882, -2), (key2993, -2), (key2592, 1), (key2595, 1), (key2848, 1), (key2970, 1), (key2882, 1), (key2991, 1), (key2602, 2), (key2912, 2), (key3003, 2), (key2379, -1), (key2393, -1), (key2407, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2395, -1), (key2483, -1), (key2526, -1), (key2545, -1), (key2565, -1), (key2382, 1), (key2395, 1), (key2410, 1), (key2445, 1), (key2545, 1), (key2557, 1)]

def rawRow2682 : Integer.Sparse Key := [(key2595, -2), (key2993, -2), (key2882, -2), (key2595, 1), (key2592, 1), (key2970, 1), (key2848, 1), (key2991, 1), (key2882, 1), (key2602, 2), (key3003, 2), (key2912, 2), (key2393, -1), (key2379, -1), (key2441, -1), (key2407, -1), (key2555, -1), (key2544, -1), (key2395, -1), (key2393, -1), (key2526, -1), (key2483, -1), (key2565, -1), (key2545, -1), (key2395, 1), (key2382, 1), (key2445, 1), (key2410, 1), (key2557, 1), (key2545, 1)]

def rawRow2683 : Integer.Sparse Key := [(key2882, -2), (key2595, -2), (key2993, -2), (key2848, 1), (key2882, 1), (key2592, 1), (key2991, 1), (key2595, 1), (key2970, 1), (key2912, 2), (key2602, 2), (key3003, 2), (key2771, -1), (key2912, -1), (key2592, -1), (key2991, -1), (key2393, -1), (key2441, -1), (key2483, -1), (key2545, -1), (key2393, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2410, 1), (key2545, 1), (key2382, 1), (key2557, 1), (key2395, 1), (key2445, 1)]

def rawRow2684 : Integer.Sparse Key := [(key2882, -2), (key2993, -2), (key2595, -2), (key2882, 1), (key2848, 1), (key2991, 1), (key2592, 1), (key2970, 1), (key2595, 1), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, -1), (key2771, -1), (key2991, -1), (key2592, -1), (key2441, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2526, -1), (key2395, -1), (key2545, 1), (key2410, 1), (key2557, 1), (key2382, 1), (key2445, 1), (key2395, 1)]

def rawRow2685 : Integer.Sparse Key := [(key2993, -2), (key2595, -2), (key2882, -2), (key2970, 1), (key2991, 1), (key2595, 1), (key2882, 1), (key2592, 1), (key2848, 1), (key3003, 2), (key2602, 2), (key2912, 2), (key2933, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2379, -1), (key2407, -1), (key2526, -1), (key2565, -1), (key2395, -1), (key2545, -1), (key2393, -1), (key2483, -1), (key2445, 1), (key2557, 1), (key2395, 1), (key2545, 1), (key2382, 1), (key2410, 1)]

def rawRow2686 : Integer.Sparse Key := [(key2993, -2), (key2882, -2), (key2595, -2), (key2991, 1), (key2970, 1), (key2882, 1), (key2595, 1), (key2848, 1), (key2592, 1), (key3003, 2), (key2912, 2), (key2602, 2), (key2991, -1), (key2933, -1), (key2912, -1), (key2602, -1), (key2771, -1), (key2592, -1), (key2565, -1), (key2526, -1), (key2545, -1), (key2395, -1), (key2483, -1), (key2393, -1), (key2557, 1), (key2445, 1), (key2545, 1), (key2395, 1), (key2410, 1), (key2382, 1)]

def rawRow2687 : Integer.Sparse Key := [(key2891, -2), (key2891, -2), (key2996, -2), (key2912, 1), (key2914, 1), (key2912, 1), (key3003, 1), (key2914, 1), (key3003, 1), (key2774, 2), (key2774, 2), (key2934, 2), (key2882, -1), (key2914, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2993, -1), (key2407, -1), (key2410, -1), (key2407, -1), (key2441, -1), (key2410, -1), (key2441, -1), (key2473, 1), (key2483, 1), (key2473, 1), (key2507, 1), (key2483, 1), (key2507, 1)]

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

def rawRow2688 : Integer.Sparse Key := [(key2891, -2), (key2996, -2), (key2891, -2), (key2914, 1), (key2912, 1), (key3003, 1), (key2912, 1), (key3003, 1), (key2914, 1), (key2774, 2), (key2934, 2), (key2774, 2), (key2914, -1), (key2882, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2410, -1), (key2407, -1), (key2441, -1), (key2407, -1), (key2441, -1), (key2410, -1), (key2483, 1), (key2473, 1), (key2507, 1), (key2473, 1), (key2507, 1), (key2483, 1)]

def rawRow2689 : Integer.Sparse Key := [(key2996, -2), (key2891, -2), (key2891, -2), (key3003, 1), (key3003, 1), (key2914, 1), (key2914, 1), (key2912, 1), (key2912, 1), (key2934, 2), (key2774, 2), (key2774, 2), (key2993, -1), (key2993, -1), (key2914, -1), (key2914, -1), (key2882, -1), (key2882, -1), (key2441, -1), (key2441, -1), (key2410, -1), (key2410, -1), (key2407, -1), (key2407, -1), (key2507, 1), (key2507, 1), (key2483, 1), (key2483, 1), (key2473, 1), (key2473, 1)]

def rawRow2690 : Integer.Sparse Key := [(key2602, -2), (key2912, -2), (key3003, -2), (key2602, 1), (key2603, 1), (key2891, 1), (key2996, 1), (key2914, 1), (key3003, 1), (key2595, 2), (key2882, 2), (key2993, 2), (key2595, -1), (key2603, -1), (key2774, -1), (key2934, -1), (key2914, -1), (key2993, -1), (key2592, -1), (key2595, -1), (key2848, -1), (key2970, -1), (key2882, -1), (key2991, -1), (key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1)]

def rawRow2691 : Integer.Sparse Key := [(key2602, -2), (key3003, -2), (key2912, -2), (key2603, 1), (key2602, 1), (key2996, 1), (key2891, 1), (key3003, 1), (key2914, 1), (key2595, 2), (key2993, 2), (key2882, 2), (key2603, -1), (key2595, -1), (key2934, -1), (key2774, -1), (key2993, -1), (key2914, -1), (key2595, -1), (key2592, -1), (key2970, -1), (key2848, -1), (key2991, -1), (key2882, -1), (key2393, 1), (key2379, 1), (key2441, 1), (key2407, 1), (key2555, 1), (key2544, 1)]

def rawRow2692 : Integer.Sparse Key := [(key2912, -2), (key2602, -2), (key3003, -2), (key2891, 1), (key2914, 1), (key2602, 1), (key3003, 1), (key2603, 1), (key2996, 1), (key2882, 2), (key2595, 2), (key2993, 2), (key2774, -1), (key2914, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2848, -1), (key2882, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2771, 1), (key2912, 1), (key2592, 1), (key2991, 1), (key2393, 1), (key2441, 1)]

def rawRow2693 : Integer.Sparse Key := [(key2912, -2), (key3003, -2), (key2602, -2), (key2914, 1), (key2891, 1), (key3003, 1), (key2602, 1), (key2996, 1), (key2603, 1), (key2882, 2), (key2993, 2), (key2595, 2), (key2914, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2934, -1), (key2603, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2970, -1), (key2595, -1), (key2912, 1), (key2771, 1), (key2991, 1), (key2592, 1), (key2441, 1), (key2393, 1)]

def rawRow2694 : Integer.Sparse Key := [(key3003, -2), (key2602, -2), (key2912, -2), (key2996, 1), (key3003, 1), (key2603, 1), (key2914, 1), (key2602, 1), (key2891, 1), (key2993, 2), (key2595, 2), (key2882, 2), (key2934, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2595, -1), (key2774, -1), (key2970, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2592, -1), (key2848, -1), (key2933, 1), (key2991, 1), (key2602, 1), (key2912, 1), (key2379, 1), (key2407, 1)]

def rawRow2695 : Integer.Sparse Key := [(key3003, -2), (key2912, -2), (key2602, -2), (key3003, 1), (key2996, 1), (key2914, 1), (key2603, 1), (key2891, 1), (key2602, 1), (key2993, 2), (key2882, 2), (key2595, 2), (key2993, -1), (key2934, -1), (key2914, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2991, -1), (key2970, -1), (key2882, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key2991, 1), (key2933, 1), (key2912, 1), (key2602, 1), (key2771, 1), (key2592, 1)]

def rawRow2720 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2383, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2484, -1), (key2484, -1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1)]

def rawRow2721 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2378, -2), (key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2484, -1), (key2472, -1), (key2484, -1), (key2472, -1), (key2480, -1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1)]

def rawRow2722 : Integer.Sparse Key := [(key2383, -2), (key2378, -2), (key2378, -2), (key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2484, -1), (key2480, -1), (key2484, -1), (key2472, -1), (key2480, -1), (key2472, -1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1)]

def rawRow2723 : Integer.Sparse Key := [(key2390, -2), (key2394, -2), (key2394, -2), (key2378, 1), (key2383, 1), (key2378, 1), (key2394, 1), (key2383, 1), (key2394, 1), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, -1), (key2411, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2443, -1), (key2503, -1), (key2509, -1), (key2503, -1), (key2524, -1), (key2509, -1), (key2524, -1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1)]

def rawRow2724 : Integer.Sparse Key := [(key2394, -2), (key2390, -2), (key2394, -2), (key2383, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2383, 1), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2503, -1), (key2524, -1), (key2503, -1), (key2524, -1), (key2509, -1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1)]

def rawRow2725 : Integer.Sparse Key := [(key2394, -2), (key2394, -2), (key2390, -2), (key2394, 1), (key2394, 1), (key2383, 1), (key2383, 1), (key2378, 1), (key2378, 1), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, -1), (key2443, -1), (key2411, -1), (key2411, -1), (key2406, -1), (key2406, -1), (key2524, -1), (key2524, -1), (key2509, -1), (key2509, -1), (key2503, -1), (key2503, -1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1)]

def rawRow2726 : Integer.Sparse Key := [(key2766, -2), (key2766, -2), (key2772, -2), (key2843, 1), (key2843, 1), (key2887, 1), (key2887, 1), (key2889, 1), (key2889, 1), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2968, -1), (key2968, -1), (key2378, -1), (key2378, -1), (key2390, -1), (key2390, -1), (key2394, -1), (key2394, -1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1)]

def rawRow2727 : Integer.Sparse Key := [(key2766, -2), (key2772, -2), (key2766, -2), (key2887, 1), (key2889, 1), (key2843, 1), (key2889, 1), (key2843, 1), (key2887, 1), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, -1), (key2968, -1), (key2843, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2390, -1), (key2394, -1), (key2378, -1), (key2394, -1), (key2378, -1), (key2390, -1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1)]

def rawRow2728 : Integer.Sparse Key := [(key2772, -2), (key2766, -2), (key2766, -2), (key2889, 1), (key2887, 1), (key2889, 1), (key2843, 1), (key2887, 1), (key2843, 1), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, -1), (key2966, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2843, -1), (key2394, -1), (key2390, -1), (key2394, -1), (key2378, -1), (key2390, -1), (key2378, -1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1)]

def rawRow2729 : Integer.Sparse Key := [(key2887, -2), (key2889, -2), (key2910, -2), (key2766, 1), (key2772, 1), (key2843, 1), (key2889, 1), (key2880, 1), (key2910, 1), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2929, -1), (key2931, -1), (key2966, -1), (key2995, -1), (key2989, -1), (key3002, -1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1)]

def rawRow2730 : Integer.Sparse Key := [(key2889, -2), (key2887, -2), (key2910, -2), (key2772, 1), (key2766, 1), (key2889, 1), (key2843, 1), (key2910, 1), (key2880, 1), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2931, -1), (key2929, -1), (key2995, -1), (key2966, -1), (key3002, -1), (key2989, -1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1)]

def rawRow2731 : Integer.Sparse Key := [(key2887, -2), (key2910, -2), (key2889, -2), (key2843, 1), (key2880, 1), (key2766, 1), (key2910, 1), (key2772, 1), (key2889, 1), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2929, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1)]

def rawRow2732 : Integer.Sparse Key := [(key2910, -2), (key2887, -2), (key2889, -2), (key2880, 1), (key2843, 1), (key2910, 1), (key2766, 1), (key2889, 1), (key2772, 1), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2989, -1), (key2966, -1), (key3002, -1), (key2929, -1), (key2995, -1), (key2931, -1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1)]

def rawRow2733 : Integer.Sparse Key := [(key2889, -2), (key2910, -2), (key2887, -2), (key2889, 1), (key2910, 1), (key2772, 1), (key2880, 1), (key2766, 1), (key2843, 1), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2995, -1), (key3002, -1), (key2931, -1), (key2989, -1), (key2929, -1), (key2966, -1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1)]

def rawRow2734 : Integer.Sparse Key := [(key2910, -2), (key2889, -2), (key2887, -2), (key2910, 1), (key2889, 1), (key2880, 1), (key2772, 1), (key2843, 1), (key2766, 1), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key3002, -1), (key2995, -1), (key2989, -1), (key2931, -1), (key2966, -1), (key2929, -1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1)]

def rawRow2735 : Integer.Sparse Key := [(key2929, -2), (key2931, -2), (key2931, -2), (key2966, 1), (key2968, 1), (key2966, 1), (key2995, 1), (key2968, 1), (key2995, 1), (key2598, 2), (key2600, 2), (key2600, 2), (key2887, -1), (key2889, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2995, -1), (key2587, -1), (key2593, -1), (key2587, -1), (key2600, -1), (key2593, -1), (key2600, -1), (key2766, 1), (key2772, 1), (key2766, 1), (key2931, 1), (key2772, 1), (key2931, 1)]

def rawRow2736 : Integer.Sparse Key := [(key2931, -2), (key2929, -2), (key2931, -2), (key2968, 1), (key2966, 1), (key2995, 1), (key2966, 1), (key2995, 1), (key2968, 1), (key2600, 2), (key2598, 2), (key2600, 2), (key2889, -1), (key2887, -1), (key2995, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2593, -1), (key2587, -1), (key2600, -1), (key2587, -1), (key2600, -1), (key2593, -1), (key2772, 1), (key2766, 1), (key2931, 1), (key2766, 1), (key2931, 1), (key2772, 1)]

def rawRow2737 : Integer.Sparse Key := [(key2931, -2), (key2931, -2), (key2929, -2), (key2995, 1), (key2995, 1), (key2968, 1), (key2968, 1), (key2966, 1), (key2966, 1), (key2600, 2), (key2600, 2), (key2598, 2), (key2995, -1), (key2995, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key2600, -1), (key2600, -1), (key2593, -1), (key2593, -1), (key2587, -1), (key2587, -1), (key2931, 1), (key2931, 1), (key2772, 1), (key2772, 1), (key2766, 1), (key2766, 1)]

def rawRow2738 : Integer.Sparse Key := [(key2966, -2), (key2968, -2), (key2989, -2), (key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2887, 2), (key2889, 2), (key2910, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2766, -1), (key2772, -1), (key2843, -1), (key2889, -1), (key2880, -1), (key2910, -1), (key2587, 1), (key2593, 1), (key2843, 1), (key2968, 1), (key2880, 1), (key2989, 1)]

def rawRow2739 : Integer.Sparse Key := [(key2968, -2), (key2966, -2), (key2989, -2), (key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2889, 2), (key2887, 2), (key2910, 2), (key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2772, -1), (key2766, -1), (key2889, -1), (key2843, -1), (key2910, -1), (key2880, -1), (key2593, 1), (key2587, 1), (key2968, 1), (key2843, 1), (key2989, 1), (key2880, 1)]

def rawRow2740 : Integer.Sparse Key := [(key2966, -2), (key2989, -2), (key2968, -2), (key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 2), (key2910, 2), (key2889, 2), (key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2843, -1), (key2880, -1), (key2766, -1), (key2910, -1), (key2772, -1), (key2889, -1), (key2843, 1), (key2880, 1), (key2587, 1), (key2989, 1), (key2593, 1), (key2968, 1)]

def rawRow2741 : Integer.Sparse Key := [(key2989, -2), (key2966, -2), (key2968, -2), (key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 2), (key2887, 2), (key2889, 2), (key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2880, -1), (key2843, -1), (key2910, -1), (key2766, -1), (key2889, -1), (key2772, -1), (key2880, 1), (key2843, 1), (key2989, 1), (key2587, 1), (key2968, 1), (key2593, 1)]

def rawRow2742 : Integer.Sparse Key := [(key2968, -2), (key2989, -2), (key2966, -2), (key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2889, 2), (key2910, 2), (key2887, 2), (key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2889, -1), (key2910, -1), (key2772, -1), (key2880, -1), (key2766, -1), (key2843, -1), (key2968, 1), (key2989, 1), (key2593, 1), (key2880, 1), (key2587, 1), (key2843, 1)]

def rawRow2743 : Integer.Sparse Key := [(key2989, -2), (key2968, -2), (key2966, -2), (key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key2910, 2), (key2889, 2), (key2887, 2), (key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2910, -1), (key2889, -1), (key2880, -1), (key2772, -1), (key2843, -1), (key2766, -1), (key2989, 1), (key2968, 1), (key2880, 1), (key2593, 1), (key2843, 1), (key2587, 1)]

def rawRow2792 : Integer.Sparse Key := [(key1531, -1), (key1531, -1), (key1765, -1), (key1765, -1), (key1768, -1), (key1768, -1), (key1536, 2), (key1768, 2), (key1768, 2), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1), (key1651, -1), (key1651, -1), (key1809, -1), (key1809, -1), (key1837, -1), (key1837, -1), (key1642, -2), (key1832, -2), (key1832, -2), (key1674, 1), (key1674, 1), (key1832, 1), (key1832, 1), (key1848, 1), (key1848, 1)]

def rawRow2793 : Integer.Sparse Key := [(key1765, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1768, 2), (key1536, 2), (key1768, 2), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1809, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1651, -1), (key1809, -1), (key1832, -2), (key1642, -2), (key1832, -2), (key1832, 1), (key1848, 1), (key1674, 1), (key1848, 1), (key1674, 1), (key1832, 1)]

def rawRow2794 : Integer.Sparse Key := [(key1768, -1), (key1765, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1531, -1), (key1768, 2), (key1768, 2), (key1536, 2), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1837, -1), (key1809, -1), (key1837, -1), (key1651, -1), (key1809, -1), (key1651, -1), (key1832, -2), (key1832, -2), (key1642, -2), (key1848, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1832, 1), (key1674, 1)]

def rawRow2795 : Integer.Sparse Key := [(key1531, -1), (key1536, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1768, -1), (key1531, 2), (key1531, 2), (key1765, 2), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1609, -1), (key1648, -1), (key1609, -1), (key1806, -1), (key1648, -1), (key1806, -1), (key1674, -2), (key1674, -2), (key1848, -2), (key1642, 1), (key1674, 1), (key1642, 1), (key1832, 1), (key1674, 1), (key1832, 1)]

def rawRow2796 : Integer.Sparse Key := [(key1536, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1531, 2), (key1765, 2), (key1531, 2), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1648, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1806, -1), (key1648, -1), (key1674, -2), (key1848, -2), (key1674, -2), (key1674, 1), (key1642, 1), (key1832, 1), (key1642, 1), (key1832, 1), (key1674, 1)]

def rawRow2797 : Integer.Sparse Key := [(key1768, -1), (key1768, -1), (key1536, -1), (key1536, -1), (key1531, -1), (key1531, -1), (key1765, 2), (key1531, 2), (key1531, 2), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1), (key1806, -1), (key1806, -1), (key1648, -1), (key1648, -1), (key1609, -1), (key1609, -1), (key1848, -2), (key1674, -2), (key1674, -2), (key1832, 1), (key1832, 1), (key1674, 1), (key1674, 1), (key1642, 1), (key1642, 1)]

def rawRow2798 : Integer.Sparse Key := [(key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1809, -1), (key1809, -1), (key1642, 2), (key1832, 2), (key1832, 2), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1), (key1674, -1), (key1674, -1), (key1832, -1), (key1832, -1), (key1848, -1), (key1848, -1), (key1536, -2), (key1768, -2), (key1768, -2), (key1651, 1), (key1651, 1), (key1809, 1), (key1809, 1), (key1837, 1), (key1837, 1)]

def rawRow2799 : Integer.Sparse Key := [(key1806, -1), (key1809, -1), (key1609, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1832, 2), (key1642, 2), (key1832, 2), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1832, -1), (key1848, -1), (key1674, -1), (key1848, -1), (key1674, -1), (key1832, -1), (key1768, -2), (key1536, -2), (key1768, -2), (key1809, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1651, 1), (key1809, 1)]

def rawRow2800 : Integer.Sparse Key := [(key1809, -1), (key1806, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1832, 2), (key1832, 2), (key1642, 2), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1), (key1848, -1), (key1832, -1), (key1848, -1), (key1674, -1), (key1832, -1), (key1674, -1), (key1768, -2), (key1768, -2), (key1536, -2), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1809, 1), (key1651, 1)]

def rawRow2801 : Integer.Sparse Key := [(key1256, -1), (key1261, -1), (key1609, -1), (key1809, -1), (key1642, -1), (key1832, -1), (key1256, 2), (key1609, 2), (key1806, 2), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1), (key1256, -1), (key1265, -1), (key1531, -1), (key1765, -1), (key1648, -1), (key1806, -1), (key1268, -2), (key1651, -2), (key1837, -2), (key1261, 1), (key1268, 1), (key1536, 1), (key1768, 1), (key1651, 1), (key1809, 1)]

def rawRow2802 : Integer.Sparse Key := [(key1261, -1), (key1256, -1), (key1809, -1), (key1609, -1), (key1832, -1), (key1642, -1), (key1256, 2), (key1806, 2), (key1609, 2), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1), (key1265, -1), (key1256, -1), (key1765, -1), (key1531, -1), (key1806, -1), (key1648, -1), (key1268, -2), (key1837, -2), (key1651, -2), (key1268, 1), (key1261, 1), (key1768, 1), (key1536, 1), (key1809, 1), (key1651, 1)]

def rawRow2803 : Integer.Sparse Key := [(key1609, -1), (key1642, -1), (key1256, -1), (key1832, -1), (key1261, -1), (key1809, -1), (key1609, 2), (key1256, 2), (key1806, 2), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1), (key1531, -1), (key1648, -1), (key1256, -1), (key1806, -1), (key1265, -1), (key1765, -1), (key1651, -2), (key1268, -2), (key1837, -2), (key1536, 1), (key1651, 1), (key1261, 1), (key1809, 1), (key1268, 1), (key1768, 1)]

def rawRow2804 : Integer.Sparse Key := [(key1642, -1), (key1609, -1), (key1832, -1), (key1256, -1), (key1809, -1), (key1261, -1), (key1609, 2), (key1806, 2), (key1256, 2), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1), (key1648, -1), (key1531, -1), (key1806, -1), (key1256, -1), (key1765, -1), (key1265, -1), (key1651, -2), (key1837, -2), (key1268, -2), (key1651, 1), (key1536, 1), (key1809, 1), (key1261, 1), (key1768, 1), (key1268, 1)]

def rawRow2805 : Integer.Sparse Key := [(key1809, -1), (key1832, -1), (key1261, -1), (key1642, -1), (key1256, -1), (key1609, -1), (key1806, 2), (key1256, 2), (key1609, 2), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1), (key1765, -1), (key1806, -1), (key1265, -1), (key1648, -1), (key1256, -1), (key1531, -1), (key1837, -2), (key1268, -2), (key1651, -2), (key1768, 1), (key1809, 1), (key1268, 1), (key1651, 1), (key1261, 1), (key1536, 1)]

def rawRow2806 : Integer.Sparse Key := [(key1832, -1), (key1809, -1), (key1642, -1), (key1261, -1), (key1609, -1), (key1256, -1), (key1806, 2), (key1609, 2), (key1256, 2), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1), (key1806, -1), (key1765, -1), (key1648, -1), (key1265, -1), (key1531, -1), (key1256, -1), (key1837, -2), (key1651, -2), (key1268, -2), (key1809, 1), (key1768, 1), (key1651, 1), (key1268, 1), (key1536, 1), (key1261, 1)]

def rawRow2807 : Integer.Sparse Key := [(key1648, -1), (key1651, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1674, 2), (key1674, 2), (key1848, 2), (key1531, 1), (key1536, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1768, 1), (key1642, -1), (key1674, -1), (key1642, -1), (key1832, -1), (key1674, -1), (key1832, -1), (key1531, -2), (key1531, -2), (key1765, -2), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1648, 1), (key1806, 1)]

def rawRow2808 : Integer.Sparse Key := [(key1651, -1), (key1648, -1), (key1837, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1674, 2), (key1848, 2), (key1674, 2), (key1536, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1674, -1), (key1642, -1), (key1832, -1), (key1642, -1), (key1832, -1), (key1674, -1), (key1531, -2), (key1765, -2), (key1531, -2), (key1648, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1806, 1), (key1648, 1)]

def rawRow2809 : Integer.Sparse Key := [(key1837, -1), (key1837, -1), (key1651, -1), (key1651, -1), (key1648, -1), (key1648, -1), (key1848, 2), (key1674, 2), (key1674, 2), (key1768, 1), (key1768, 1), (key1536, 1), (key1536, 1), (key1531, 1), (key1531, 1), (key1832, -1), (key1832, -1), (key1674, -1), (key1674, -1), (key1642, -1), (key1642, -1), (key1765, -2), (key1531, -2), (key1531, -2), (key1806, 1), (key1806, 1), (key1648, 1), (key1648, 1), (key1609, 1), (key1609, 1)]

def rawRow2810 : Integer.Sparse Key := [(key1265, -1), (key1268, -1), (key1648, -1), (key1837, -1), (key1674, -1), (key1848, -1), (key1268, 2), (key1651, 2), (key1837, 2), (key1256, 1), (key1261, 1), (key1609, 1), (key1809, 1), (key1642, 1), (key1832, 1), (key1261, -1), (key1268, -1), (key1536, -1), (key1768, -1), (key1651, -1), (key1809, -1), (key1256, -2), (key1609, -2), (key1806, -2), (key1256, 1), (key1265, 1), (key1531, 1), (key1765, 1), (key1648, 1), (key1806, 1)]

def rawRow2811 : Integer.Sparse Key := [(key1268, -1), (key1265, -1), (key1837, -1), (key1648, -1), (key1848, -1), (key1674, -1), (key1268, 2), (key1837, 2), (key1651, 2), (key1261, 1), (key1256, 1), (key1809, 1), (key1609, 1), (key1832, 1), (key1642, 1), (key1268, -1), (key1261, -1), (key1768, -1), (key1536, -1), (key1809, -1), (key1651, -1), (key1256, -2), (key1806, -2), (key1609, -2), (key1265, 1), (key1256, 1), (key1765, 1), (key1531, 1), (key1806, 1), (key1648, 1)]

def rawRow2812 : Integer.Sparse Key := [(key1648, -1), (key1674, -1), (key1265, -1), (key1848, -1), (key1268, -1), (key1837, -1), (key1651, 2), (key1268, 2), (key1837, 2), (key1609, 1), (key1642, 1), (key1256, 1), (key1832, 1), (key1261, 1), (key1809, 1), (key1536, -1), (key1651, -1), (key1261, -1), (key1809, -1), (key1268, -1), (key1768, -1), (key1609, -2), (key1256, -2), (key1806, -2), (key1531, 1), (key1648, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1765, 1)]

def rawRow2813 : Integer.Sparse Key := [(key1674, -1), (key1648, -1), (key1848, -1), (key1265, -1), (key1837, -1), (key1268, -1), (key1651, 2), (key1837, 2), (key1268, 2), (key1642, 1), (key1609, 1), (key1832, 1), (key1256, 1), (key1809, 1), (key1261, 1), (key1651, -1), (key1536, -1), (key1809, -1), (key1261, -1), (key1768, -1), (key1268, -1), (key1609, -2), (key1806, -2), (key1256, -2), (key1648, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1765, 1), (key1265, 1)]

def rawRow2814 : Integer.Sparse Key := [(key1837, -1), (key1848, -1), (key1268, -1), (key1674, -1), (key1265, -1), (key1648, -1), (key1837, 2), (key1268, 2), (key1651, 2), (key1809, 1), (key1832, 1), (key1261, 1), (key1642, 1), (key1256, 1), (key1609, 1), (key1768, -1), (key1809, -1), (key1268, -1), (key1651, -1), (key1261, -1), (key1536, -1), (key1806, -2), (key1256, -2), (key1609, -2), (key1765, 1), (key1806, 1), (key1265, 1), (key1648, 1), (key1256, 1), (key1531, 1)]

def rawRow2815 : Integer.Sparse Key := [(key1848, -1), (key1837, -1), (key1674, -1), (key1268, -1), (key1648, -1), (key1265, -1), (key1837, 2), (key1651, 2), (key1268, 2), (key1832, 1), (key1809, 1), (key1642, 1), (key1261, 1), (key1609, 1), (key1256, 1), (key1809, -1), (key1768, -1), (key1651, -1), (key1268, -1), (key1536, -1), (key1261, -1), (key1806, -2), (key1609, -2), (key1256, -2), (key1806, 1), (key1765, 1), (key1648, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

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

def rawRow2816 : Integer.Sparse Key := [(key2428, -2), (key2428, -2), (key2444, -2), (key2430, 2), (key2430, 2), (key2444, 2), (key2496, 2), (key2496, 2), (key2510, 2), (key2510, -6), (key2574, -2), (key2574, -2), (key2577, -2), (key2577, 6)]

def rawRow2817 : Integer.Sparse Key := [(key2428, -2), (key2444, -2), (key2428, -2), (key2430, 2), (key2444, 2), (key2430, 2), (key2496, 2), (key2510, 2), (key2496, 2), (key2510, -6), (key2574, -2), (key2577, -2), (key2574, -2), (key2577, 6)]

def rawRow2818 : Integer.Sparse Key := [(key2444, -2), (key2428, -2), (key2428, -2), (key2444, 2), (key2430, 2), (key2430, 2), (key2510, 2), (key2496, 2), (key2496, 2), (key2510, -6), (key2577, -2), (key2574, -2), (key2574, -2), (key2577, 6)]

def rawRow2822 : Integer.Sparse Key := [(key3132, -2), (key3132, -2), (key3145, -2), (key3140, 2), (key3140, 2), (key3148, 2), (key2428, 2), (key2428, 2), (key2444, 2), (key2577, -6), (key2430, -2), (key2430, -2), (key2444, -2), (key2510, 6)]

def rawRow2823 : Integer.Sparse Key := [(key3132, -2), (key3145, -2), (key3132, -2), (key3140, 2), (key3148, 2), (key3140, 2), (key2428, 2), (key2444, 2), (key2428, 2), (key2577, -6), (key2430, -2), (key2444, -2), (key2430, -2), (key2510, 6)]

def rawRow2824 : Integer.Sparse Key := [(key3145, -2), (key3132, -2), (key3132, -2), (key3148, 2), (key3140, 2), (key3140, 2), (key2444, 2), (key2428, 2), (key2428, 2), (key2577, -6), (key2444, -2), (key2430, -2), (key2430, -2), (key2510, 6)]

def rawRow2840 : Integer.Sparse Key := [(key1256, -2), (key1256, -2), (key1261, -2), (key1256, 1), (key1256, 1), (key1265, 1), (key1265, 1), (key1268, 1), (key1268, 1), (key1531, 2), (key1531, 2), (key1536, 2), (key1531, -1), (key1531, -1), (key1765, -1), (key1765, -1), (key1768, -1), (key1768, -1), (key1609, -1), (key1609, -1), (key1648, -1), (key1648, -1), (key1651, -1), (key1651, -1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1)]

def rawRow2841 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1256, -2), (key1265, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1531, 2), (key1536, 2), (key1531, 2), (key1765, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1648, -1), (key1651, -1), (key1609, -1), (key1651, -1), (key1609, -1), (key1648, -1), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1)]

def rawRow2842 : Integer.Sparse Key := [(key1261, -2), (key1256, -2), (key1256, -2), (key1268, 1), (key1265, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1256, 1), (key1536, 2), (key1531, 2), (key1531, 2), (key1768, -1), (key1765, -1), (key1768, -1), (key1531, -1), (key1765, -1), (key1531, -1), (key1651, -1), (key1648, -1), (key1651, -1), (key1609, -1), (key1648, -1), (key1609, -1), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1)]

def rawRow2843 : Integer.Sparse Key := [(key1265, -2), (key1268, -2), (key1268, -2), (key1256, 1), (key1261, 1), (key1256, 1), (key1268, 1), (key1261, 1), (key1268, 1), (key1765, 2), (key1768, 2), (key1768, 2), (key1531, -1), (key1536, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1768, -1), (key1806, -1), (key1809, -1), (key1806, -1), (key1837, -1), (key1809, -1), (key1837, -1), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1)]

def rawRow2844 : Integer.Sparse Key := [(key1268, -2), (key1265, -2), (key1268, -2), (key1261, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1261, 1), (key1768, 2), (key1765, 2), (key1768, 2), (key1536, -1), (key1531, -1), (key1768, -1), (key1531, -1), (key1768, -1), (key1536, -1), (key1809, -1), (key1806, -1), (key1837, -1), (key1806, -1), (key1837, -1), (key1809, -1), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1)]

def rawRow2845 : Integer.Sparse Key := [(key1268, -2), (key1268, -2), (key1265, -2), (key1268, 1), (key1268, 1), (key1261, 1), (key1261, 1), (key1256, 1), (key1256, 1), (key1768, 2), (key1768, 2), (key1765, 2), (key1768, -1), (key1768, -1), (key1536, -1), (key1536, -1), (key1531, -1), (key1531, -1), (key1837, -1), (key1837, -1), (key1809, -1), (key1809, -1), (key1806, -1), (key1806, -1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1)]

def rawRow2846 : Integer.Sparse Key := [(key1531, -2), (key1531, -2), (key1536, -2), (key1609, 1), (key1609, 1), (key1648, 1), (key1648, 1), (key1651, 1), (key1651, 1), (key1256, 2), (key1256, 2), (key1261, 2), (key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1809, -1), (key1809, -1), (key1256, -1), (key1256, -1), (key1265, -1), (key1265, -1), (key1268, -1), (key1268, -1), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1)]

def rawRow2847 : Integer.Sparse Key := [(key1531, -2), (key1536, -2), (key1531, -2), (key1648, 1), (key1651, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1256, 2), (key1261, 2), (key1256, 2), (key1806, -1), (key1809, -1), (key1609, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1265, -1), (key1268, -1), (key1256, -1), (key1268, -1), (key1256, -1), (key1265, -1), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1)]

def rawRow2848 : Integer.Sparse Key := [(key1536, -2), (key1531, -2), (key1531, -2), (key1651, 1), (key1648, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1261, 2), (key1256, 2), (key1256, 2), (key1809, -1), (key1806, -1), (key1809, -1), (key1609, -1), (key1806, -1), (key1609, -1), (key1268, -1), (key1265, -1), (key1268, -1), (key1256, -1), (key1265, -1), (key1256, -1), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1)]

def rawRow2849 : Integer.Sparse Key := [(key1648, -2), (key1651, -2), (key1674, -2), (key1531, 1), (key1536, 1), (key1609, 1), (key1651, 1), (key1642, 1), (key1674, 1), (key1806, 2), (key1809, 2), (key1832, 2), (key1256, -1), (key1261, -1), (key1609, -1), (key1809, -1), (key1642, -1), (key1832, -1), (key1765, -1), (key1768, -1), (key1806, -1), (key1837, -1), (key1832, -1), (key1848, -1), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1)]

def rawRow2850 : Integer.Sparse Key := [(key1651, -2), (key1648, -2), (key1674, -2), (key1536, 1), (key1531, 1), (key1651, 1), (key1609, 1), (key1674, 1), (key1642, 1), (key1809, 2), (key1806, 2), (key1832, 2), (key1261, -1), (key1256, -1), (key1809, -1), (key1609, -1), (key1832, -1), (key1642, -1), (key1768, -1), (key1765, -1), (key1837, -1), (key1806, -1), (key1848, -1), (key1832, -1), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1)]

def rawRow2851 : Integer.Sparse Key := [(key1648, -2), (key1674, -2), (key1651, -2), (key1609, 1), (key1642, 1), (key1531, 1), (key1674, 1), (key1536, 1), (key1651, 1), (key1806, 2), (key1832, 2), (key1809, 2), (key1609, -1), (key1642, -1), (key1256, -1), (key1832, -1), (key1261, -1), (key1809, -1), (key1806, -1), (key1832, -1), (key1765, -1), (key1848, -1), (key1768, -1), (key1837, -1), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1)]

def rawRow2852 : Integer.Sparse Key := [(key1674, -2), (key1648, -2), (key1651, -2), (key1642, 1), (key1609, 1), (key1674, 1), (key1531, 1), (key1651, 1), (key1536, 1), (key1832, 2), (key1806, 2), (key1809, 2), (key1642, -1), (key1609, -1), (key1832, -1), (key1256, -1), (key1809, -1), (key1261, -1), (key1832, -1), (key1806, -1), (key1848, -1), (key1765, -1), (key1837, -1), (key1768, -1), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1)]

def rawRow2853 : Integer.Sparse Key := [(key1651, -2), (key1674, -2), (key1648, -2), (key1651, 1), (key1674, 1), (key1536, 1), (key1642, 1), (key1531, 1), (key1609, 1), (key1809, 2), (key1832, 2), (key1806, 2), (key1809, -1), (key1832, -1), (key1261, -1), (key1642, -1), (key1256, -1), (key1609, -1), (key1837, -1), (key1848, -1), (key1768, -1), (key1832, -1), (key1765, -1), (key1806, -1), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1)]

def rawRow2854 : Integer.Sparse Key := [(key1674, -2), (key1651, -2), (key1648, -2), (key1674, 1), (key1651, 1), (key1642, 1), (key1536, 1), (key1609, 1), (key1531, 1), (key1832, 2), (key1809, 2), (key1806, 2), (key1832, -1), (key1809, -1), (key1642, -1), (key1261, -1), (key1609, -1), (key1256, -1), (key1848, -1), (key1837, -1), (key1832, -1), (key1768, -1), (key1806, -1), (key1765, -1), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1)]

def rawRow2855 : Integer.Sparse Key := [(key1765, -2), (key1768, -2), (key1768, -2), (key1806, 1), (key1809, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1265, 2), (key1268, 2), (key1268, 2), (key1648, -1), (key1651, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1837, -1), (key1256, -1), (key1261, -1), (key1256, -1), (key1268, -1), (key1261, -1), (key1268, -1), (key1531, 1), (key1536, 1), (key1531, 1), (key1768, 1), (key1536, 1), (key1768, 1)]

def rawRow2856 : Integer.Sparse Key := [(key1768, -2), (key1765, -2), (key1768, -2), (key1809, 1), (key1806, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1268, 2), (key1265, 2), (key1268, 2), (key1651, -1), (key1648, -1), (key1837, -1), (key1648, -1), (key1837, -1), (key1651, -1), (key1261, -1), (key1256, -1), (key1268, -1), (key1256, -1), (key1268, -1), (key1261, -1), (key1536, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1536, 1)]

def rawRow2857 : Integer.Sparse Key := [(key1768, -2), (key1768, -2), (key1765, -2), (key1837, 1), (key1837, 1), (key1809, 1), (key1809, 1), (key1806, 1), (key1806, 1), (key1268, 2), (key1268, 2), (key1265, 2), (key1837, -1), (key1837, -1), (key1651, -1), (key1651, -1), (key1648, -1), (key1648, -1), (key1268, -1), (key1268, -1), (key1261, -1), (key1261, -1), (key1256, -1), (key1256, -1), (key1768, 1), (key1768, 1), (key1536, 1), (key1536, 1), (key1531, 1), (key1531, 1)]

def rawRow2858 : Integer.Sparse Key := [(key1806, -2), (key1809, -2), (key1832, -2), (key1765, 1), (key1768, 1), (key1806, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1648, 2), (key1651, 2), (key1674, 2), (key1265, -1), (key1268, -1), (key1648, -1), (key1837, -1), (key1674, -1), (key1848, -1), (key1531, -1), (key1536, -1), (key1609, -1), (key1651, -1), (key1642, -1), (key1674, -1), (key1256, 1), (key1261, 1), (key1609, 1), (key1809, 1), (key1642, 1), (key1832, 1)]

def rawRow2859 : Integer.Sparse Key := [(key1809, -2), (key1806, -2), (key1832, -2), (key1768, 1), (key1765, 1), (key1837, 1), (key1806, 1), (key1848, 1), (key1832, 1), (key1651, 2), (key1648, 2), (key1674, 2), (key1268, -1), (key1265, -1), (key1837, -1), (key1648, -1), (key1848, -1), (key1674, -1), (key1536, -1), (key1531, -1), (key1651, -1), (key1609, -1), (key1674, -1), (key1642, -1), (key1261, 1), (key1256, 1), (key1809, 1), (key1609, 1), (key1832, 1), (key1642, 1)]

def rawRow2860 : Integer.Sparse Key := [(key1806, -2), (key1832, -2), (key1809, -2), (key1806, 1), (key1832, 1), (key1765, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1648, 2), (key1674, 2), (key1651, 2), (key1648, -1), (key1674, -1), (key1265, -1), (key1848, -1), (key1268, -1), (key1837, -1), (key1609, -1), (key1642, -1), (key1531, -1), (key1674, -1), (key1536, -1), (key1651, -1), (key1609, 1), (key1642, 1), (key1256, 1), (key1832, 1), (key1261, 1), (key1809, 1)]

def rawRow2861 : Integer.Sparse Key := [(key1832, -2), (key1806, -2), (key1809, -2), (key1832, 1), (key1806, 1), (key1848, 1), (key1765, 1), (key1837, 1), (key1768, 1), (key1674, 2), (key1648, 2), (key1651, 2), (key1674, -1), (key1648, -1), (key1848, -1), (key1265, -1), (key1837, -1), (key1268, -1), (key1642, -1), (key1609, -1), (key1674, -1), (key1531, -1), (key1651, -1), (key1536, -1), (key1642, 1), (key1609, 1), (key1832, 1), (key1256, 1), (key1809, 1), (key1261, 1)]

def rawRow2862 : Integer.Sparse Key := [(key1809, -2), (key1832, -2), (key1806, -2), (key1837, 1), (key1848, 1), (key1768, 1), (key1832, 1), (key1765, 1), (key1806, 1), (key1651, 2), (key1674, 2), (key1648, 2), (key1837, -1), (key1848, -1), (key1268, -1), (key1674, -1), (key1265, -1), (key1648, -1), (key1651, -1), (key1674, -1), (key1536, -1), (key1642, -1), (key1531, -1), (key1609, -1), (key1809, 1), (key1832, 1), (key1261, 1), (key1642, 1), (key1256, 1), (key1609, 1)]

def rawRow2863 : Integer.Sparse Key := [(key1832, -2), (key1809, -2), (key1806, -2), (key1848, 1), (key1837, 1), (key1832, 1), (key1768, 1), (key1806, 1), (key1765, 1), (key1674, 2), (key1651, 2), (key1648, 2), (key1848, -1), (key1837, -1), (key1674, -1), (key1268, -1), (key1648, -1), (key1265, -1), (key1674, -1), (key1651, -1), (key1642, -1), (key1536, -1), (key1609, -1), (key1531, -1), (key1832, 1), (key1809, 1), (key1642, 1), (key1261, 1), (key1609, 1), (key1256, 1)]

def rawRow2888 : Integer.Sparse Key := [(key2379, -2), (key2393, -2), (key2393, -2), (key2382, 1), (key2382, 1), (key2393, 1), (key2393, 1), (key2395, 1), (key2395, 1), (key2473, 2), (key2483, 2), (key2483, 2), (key2483, -1), (key2483, -1), (key2507, -1), (key2507, -1), (key2526, -1), (key2526, -1), (key2539, -1), (key2539, -1), (key2544, -1), (key2544, -1), (key2545, -1), (key2545, -1), (key2544, 1), (key2544, 1), (key2555, 1), (key2555, 1), (key2565, 1), (key2565, 1)]

def rawRow2889 : Integer.Sparse Key := [(key2393, -2), (key2379, -2), (key2393, -2), (key2393, 1), (key2395, 1), (key2382, 1), (key2395, 1), (key2382, 1), (key2393, 1), (key2483, 2), (key2473, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2483, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2544, -1), (key2545, -1), (key2539, -1), (key2545, -1), (key2539, -1), (key2544, -1), (key2555, 1), (key2565, 1), (key2544, 1), (key2565, 1), (key2544, 1), (key2555, 1)]

def rawRow2890 : Integer.Sparse Key := [(key2393, -2), (key2393, -2), (key2379, -2), (key2395, 1), (key2393, 1), (key2395, 1), (key2382, 1), (key2393, 1), (key2382, 1), (key2483, 2), (key2483, 2), (key2473, 2), (key2526, -1), (key2507, -1), (key2526, -1), (key2483, -1), (key2507, -1), (key2483, -1), (key2545, -1), (key2544, -1), (key2545, -1), (key2539, -1), (key2544, -1), (key2539, -1), (key2565, 1), (key2555, 1), (key2565, 1), (key2544, 1), (key2555, 1), (key2544, 1)]

def rawRow2891 : Integer.Sparse Key := [(key2382, -2), (key2382, -2), (key2395, -2), (key2379, 1), (key2382, 1), (key2379, 1), (key2393, 1), (key2382, 1), (key2393, 1), (key2507, 2), (key2507, 2), (key2526, 2), (key2473, -1), (key2483, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2507, -1), (key2555, -1), (key2557, -1), (key2555, -1), (key2565, -1), (key2557, -1), (key2565, -1), (key2539, 1), (key2545, 1), (key2539, 1), (key2557, 1), (key2545, 1), (key2557, 1)]

def rawRow2892 : Integer.Sparse Key := [(key2382, -2), (key2395, -2), (key2382, -2), (key2382, 1), (key2379, 1), (key2393, 1), (key2379, 1), (key2393, 1), (key2382, 1), (key2507, 2), (key2526, 2), (key2507, 2), (key2483, -1), (key2473, -1), (key2507, -1), (key2473, -1), (key2507, -1), (key2483, -1), (key2557, -1), (key2555, -1), (key2565, -1), (key2555, -1), (key2565, -1), (key2557, -1), (key2545, 1), (key2539, 1), (key2557, 1), (key2539, 1), (key2557, 1), (key2545, 1)]

def rawRow2893 : Integer.Sparse Key := [(key2395, -2), (key2382, -2), (key2382, -2), (key2393, 1), (key2393, 1), (key2382, 1), (key2382, 1), (key2379, 1), (key2379, 1), (key2526, 2), (key2507, 2), (key2507, 2), (key2507, -1), (key2507, -1), (key2483, -1), (key2483, -1), (key2473, -1), (key2473, -1), (key2565, -1), (key2565, -1), (key2557, -1), (key2557, -1), (key2555, -1), (key2555, -1), (key2557, 1), (key2557, 1), (key2545, 1), (key2545, 1), (key2539, 1), (key2539, 1)]

def rawRow2894 : Integer.Sparse Key := [(key2848, -2), (key2891, -2), (key2891, -2), (key2882, 1), (key2882, 1), (key2912, 1), (key2912, 1), (key2914, 1), (key2914, 1), (key2379, 2), (key2393, 2), (key2393, 2), (key2544, -1), (key2544, -1), (key2555, -1), (key2555, -1), (key2565, -1), (key2565, -1), (key2382, -1), (key2382, -1), (key2393, -1), (key2393, -1), (key2395, -1), (key2395, -1), (key2483, 1), (key2483, 1), (key2507, 1), (key2507, 1), (key2526, 1), (key2526, 1)]

def rawRow2895 : Integer.Sparse Key := [(key2891, -2), (key2848, -2), (key2891, -2), (key2912, 1), (key2914, 1), (key2882, 1), (key2914, 1), (key2882, 1), (key2912, 1), (key2393, 2), (key2379, 2), (key2393, 2), (key2555, -1), (key2565, -1), (key2544, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2395, -1), (key2382, -1), (key2395, -1), (key2382, -1), (key2393, -1), (key2507, 1), (key2526, 1), (key2483, 1), (key2526, 1), (key2483, 1), (key2507, 1)]

def rawRow2896 : Integer.Sparse Key := [(key2891, -2), (key2891, -2), (key2848, -2), (key2914, 1), (key2912, 1), (key2914, 1), (key2882, 1), (key2912, 1), (key2882, 1), (key2393, 2), (key2393, 2), (key2379, 2), (key2565, -1), (key2555, -1), (key2565, -1), (key2544, -1), (key2555, -1), (key2544, -1), (key2395, -1), (key2393, -1), (key2395, -1), (key2382, -1), (key2393, -1), (key2382, -1), (key2526, 1), (key2507, 1), (key2526, 1), (key2483, 1), (key2507, 1), (key2483, 1)]

def rawRow2897 : Integer.Sparse Key := [(key2774, -2), (key2882, -2), (key2914, -2), (key2771, 1), (key2774, 1), (key2848, 1), (key2891, 1), (key2882, 1), (key2912, 1), (key2933, 2), (key2991, 2), (key3003, 2), (key2379, -1), (key2393, -1), (key2407, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2441, -1), (key2445, -1), (key2507, -1), (key2526, -1), (key2557, -1), (key2565, -1), (key2382, 1), (key2395, 1), (key2410, 1), (key2445, 1), (key2545, 1), (key2557, 1)]

def rawRow2898 : Integer.Sparse Key := [(key2774, -2), (key2914, -2), (key2882, -2), (key2774, 1), (key2771, 1), (key2891, 1), (key2848, 1), (key2912, 1), (key2882, 1), (key2933, 2), (key3003, 2), (key2991, 2), (key2393, -1), (key2379, -1), (key2441, -1), (key2407, -1), (key2555, -1), (key2544, -1), (key2445, -1), (key2441, -1), (key2526, -1), (key2507, -1), (key2565, -1), (key2557, -1), (key2395, 1), (key2382, 1), (key2445, 1), (key2410, 1), (key2557, 1), (key2545, 1)]

def rawRow2899 : Integer.Sparse Key := [(key2882, -2), (key2774, -2), (key2914, -2), (key2848, 1), (key2882, 1), (key2771, 1), (key2912, 1), (key2774, 1), (key2891, 1), (key2991, 2), (key2933, 2), (key3003, 2), (key2771, -1), (key2912, -1), (key2592, -1), (key2991, -1), (key2393, -1), (key2441, -1), (key2507, -1), (key2557, -1), (key2441, -1), (key2565, -1), (key2445, -1), (key2526, -1), (key2410, 1), (key2545, 1), (key2382, 1), (key2557, 1), (key2395, 1), (key2445, 1)]

def rawRow2900 : Integer.Sparse Key := [(key2882, -2), (key2914, -2), (key2774, -2), (key2882, 1), (key2848, 1), (key2912, 1), (key2771, 1), (key2891, 1), (key2774, 1), (key2991, 2), (key3003, 2), (key2933, 2), (key2912, -1), (key2771, -1), (key2991, -1), (key2592, -1), (key2441, -1), (key2393, -1), (key2557, -1), (key2507, -1), (key2565, -1), (key2441, -1), (key2526, -1), (key2445, -1), (key2545, 1), (key2410, 1), (key2557, 1), (key2382, 1), (key2445, 1), (key2395, 1)]

def rawRow2901 : Integer.Sparse Key := [(key2914, -2), (key2774, -2), (key2882, -2), (key2891, 1), (key2912, 1), (key2774, 1), (key2882, 1), (key2771, 1), (key2848, 1), (key3003, 2), (key2933, 2), (key2991, 2), (key2933, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2379, -1), (key2407, -1), (key2526, -1), (key2565, -1), (key2445, -1), (key2557, -1), (key2441, -1), (key2507, -1), (key2445, 1), (key2557, 1), (key2395, 1), (key2545, 1), (key2382, 1), (key2410, 1)]

def rawRow2902 : Integer.Sparse Key := [(key2914, -2), (key2882, -2), (key2774, -2), (key2912, 1), (key2891, 1), (key2882, 1), (key2774, 1), (key2848, 1), (key2771, 1), (key3003, 2), (key2991, 2), (key2933, 2), (key2991, -1), (key2933, -1), (key2912, -1), (key2602, -1), (key2771, -1), (key2592, -1), (key2565, -1), (key2526, -1), (key2557, -1), (key2445, -1), (key2507, -1), (key2441, -1), (key2557, 1), (key2445, 1), (key2545, 1), (key2395, 1), (key2410, 1), (key2382, 1)]

def rawRow2903 : Integer.Sparse Key := [(key2970, -2), (key2970, -2), (key2996, -2), (key2991, 1), (key2993, 1), (key2991, 1), (key3003, 1), (key2993, 1), (key3003, 1), (key2595, 2), (key2595, 2), (key2603, 2), (key2882, -1), (key2914, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2993, -1), (key2379, -1), (key2382, -1), (key2379, -1), (key2393, -1), (key2382, -1), (key2393, -1), (key2473, 1), (key2483, 1), (key2473, 1), (key2507, 1), (key2483, 1), (key2507, 1)]

def rawRow2904 : Integer.Sparse Key := [(key2970, -2), (key2996, -2), (key2970, -2), (key2993, 1), (key2991, 1), (key3003, 1), (key2991, 1), (key3003, 1), (key2993, 1), (key2595, 2), (key2603, 2), (key2595, 2), (key2914, -1), (key2882, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2914, -1), (key2382, -1), (key2379, -1), (key2393, -1), (key2379, -1), (key2393, -1), (key2382, -1), (key2483, 1), (key2473, 1), (key2507, 1), (key2473, 1), (key2507, 1), (key2483, 1)]

def rawRow2905 : Integer.Sparse Key := [(key2996, -2), (key2970, -2), (key2970, -2), (key3003, 1), (key3003, 1), (key2993, 1), (key2993, 1), (key2991, 1), (key2991, 1), (key2603, 2), (key2595, 2), (key2595, 2), (key2993, -1), (key2993, -1), (key2914, -1), (key2914, -1), (key2882, -1), (key2882, -1), (key2393, -1), (key2393, -1), (key2382, -1), (key2382, -1), (key2379, -1), (key2379, -1), (key2507, 1), (key2507, 1), (key2483, 1), (key2483, 1), (key2473, 1), (key2473, 1)]

def rawRow2906 : Integer.Sparse Key := [(key2933, -2), (key2991, -2), (key3003, -2), (key2933, 1), (key2934, 1), (key2970, 1), (key2996, 1), (key2993, 1), (key3003, 1), (key2774, 2), (key2882, 2), (key2914, 2), (key2595, -1), (key2603, -1), (key2774, -1), (key2934, -1), (key2914, -1), (key2993, -1), (key2771, -1), (key2774, -1), (key2848, -1), (key2891, -1), (key2882, -1), (key2912, -1), (key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1)]

def rawRow2907 : Integer.Sparse Key := [(key2933, -2), (key3003, -2), (key2991, -2), (key2934, 1), (key2933, 1), (key2996, 1), (key2970, 1), (key3003, 1), (key2993, 1), (key2774, 2), (key2914, 2), (key2882, 2), (key2603, -1), (key2595, -1), (key2934, -1), (key2774, -1), (key2993, -1), (key2914, -1), (key2774, -1), (key2771, -1), (key2891, -1), (key2848, -1), (key2912, -1), (key2882, -1), (key2393, 1), (key2379, 1), (key2441, 1), (key2407, 1), (key2555, 1), (key2544, 1)]

def rawRow2908 : Integer.Sparse Key := [(key2991, -2), (key2933, -2), (key3003, -2), (key2970, 1), (key2993, 1), (key2933, 1), (key3003, 1), (key2934, 1), (key2996, 1), (key2882, 2), (key2774, 2), (key2914, 2), (key2774, -1), (key2914, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2848, -1), (key2882, -1), (key2771, -1), (key2912, -1), (key2774, -1), (key2891, -1), (key2771, 1), (key2912, 1), (key2592, 1), (key2991, 1), (key2393, 1), (key2441, 1)]

def rawRow2909 : Integer.Sparse Key := [(key2991, -2), (key3003, -2), (key2933, -2), (key2993, 1), (key2970, 1), (key3003, 1), (key2933, 1), (key2996, 1), (key2934, 1), (key2882, 2), (key2914, 2), (key2774, 2), (key2914, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2934, -1), (key2603, -1), (key2882, -1), (key2848, -1), (key2912, -1), (key2771, -1), (key2891, -1), (key2774, -1), (key2912, 1), (key2771, 1), (key2991, 1), (key2592, 1), (key2441, 1), (key2393, 1)]

def rawRow2910 : Integer.Sparse Key := [(key3003, -2), (key2933, -2), (key2991, -2), (key2996, 1), (key3003, 1), (key2934, 1), (key2993, 1), (key2933, 1), (key2970, 1), (key2914, 2), (key2774, 2), (key2882, 2), (key2934, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2595, -1), (key2774, -1), (key2891, -1), (key2912, -1), (key2774, -1), (key2882, -1), (key2771, -1), (key2848, -1), (key2933, 1), (key2991, 1), (key2602, 1), (key2912, 1), (key2379, 1), (key2407, 1)]

def rawRow2911 : Integer.Sparse Key := [(key3003, -2), (key2991, -2), (key2933, -2), (key3003, 1), (key2996, 1), (key2993, 1), (key2934, 1), (key2970, 1), (key2933, 1), (key2914, 2), (key2882, 2), (key2774, 2), (key2993, -1), (key2934, -1), (key2914, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2912, -1), (key2891, -1), (key2882, -1), (key2774, -1), (key2848, -1), (key2771, -1), (key2991, 1), (key2933, 1), (key2912, 1), (key2602, 1), (key2771, 1), (key2592, 1)]

def rawRow2939 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2364, -2), (key2361, 6), (key2517, 2), (key2520, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2561, -6), (key2531, 2), (key2531, 2), (key2561, 2)]

def rawRow2940 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2364, -2), (key2361, 6), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2561, -6), (key2531, 2), (key2561, 2), (key2531, 2)]

def rawRow2941 : Integer.Sparse Key := [(key2364, -2), (key2364, -2), (key2361, -2), (key2361, 6), (key2520, 2), (key2520, 2), (key2517, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2561, -6), (key2561, 2), (key2531, 2), (key2531, 2)]

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

def rawRow2951 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2520, -2), (key2561, 6), (key2361, 2), (key2364, 2), (key2364, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2361, -6), (key2456, 2), (key2456, 2), (key2517, 2)]

def rawRow2952 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2520, -2), (key2561, 6), (key2364, 2), (key2361, 2), (key2364, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2361, -6), (key2456, 2), (key2517, 2), (key2456, 2)]

def rawRow2953 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2517, -2), (key2561, 6), (key2364, 2), (key2364, 2), (key2361, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2361, -6), (key2517, 2), (key2456, 2), (key2456, 2)]

def rawRow2960 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 2), (key2406, 2), (key2409, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2482, -1), (key2482, -1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1)]

def rawRow2961 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2406, 2), (key2409, 2), (key2406, 2), (key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2482, -1), (key2472, -1), (key2482, -1), (key2472, -1), (key2480, -1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1)]

def rawRow2962 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2409, 2), (key2406, 2), (key2406, 2), (key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2482, -1), (key2480, -1), (key2482, -1), (key2472, -1), (key2480, -1), (key2472, -1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1)]

def rawRow2963 : Integer.Sparse Key := [(key2390, -2), (key2392, -2), (key2392, -2), (key2378, 1), (key2381, 1), (key2378, 1), (key2392, 1), (key2381, 1), (key2392, 1), (key2437, 2), (key2440, 2), (key2440, 2), (key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2503, -1), (key2506, -1), (key2503, -1), (key2522, -1), (key2506, -1), (key2522, -1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1)]

def rawRow2964 : Integer.Sparse Key := [(key2392, -2), (key2390, -2), (key2392, -2), (key2381, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2381, 1), (key2440, 2), (key2437, 2), (key2440, 2), (key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2503, -1), (key2522, -1), (key2503, -1), (key2522, -1), (key2506, -1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1)]

def rawRow2965 : Integer.Sparse Key := [(key2392, -2), (key2392, -2), (key2390, -2), (key2392, 1), (key2392, 1), (key2381, 1), (key2381, 1), (key2378, 1), (key2378, 1), (key2440, 2), (key2440, 2), (key2437, 2), (key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2522, -1), (key2522, -1), (key2506, -1), (key2506, -1), (key2503, -1), (key2503, -1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1)]

def rawRow2966 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2378, 2), (key2378, 2), (key2381, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2378, -1), (key2378, -1), (key2390, -1), (key2390, -1), (key2392, -1), (key2392, -1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1)]

def rawRow2967 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2378, 2), (key2381, 2), (key2378, 2), (key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2390, -1), (key2392, -1), (key2378, -1), (key2392, -1), (key2378, -1), (key2390, -1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1)]

def rawRow2968 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2381, 2), (key2378, 2), (key2378, 2), (key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2392, -1), (key2390, -1), (key2392, -1), (key2378, -1), (key2390, -1), (key2378, -1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1)]

def rawRow2969 : Integer.Sparse Key := [(key2480, -2), (key2482, -2), (key2543, -2), (key2406, 1), (key2409, 1), (key2472, 1), (key2482, 1), (key2538, 1), (key2543, 1), (key2503, 2), (key2506, 2), (key2554, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2437, -1), (key2440, -1), (key2503, -1), (key2522, -1), (key2554, -1), (key2563, -1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1)]

def rawRow2970 : Integer.Sparse Key := [(key2482, -2), (key2480, -2), (key2543, -2), (key2409, 1), (key2406, 1), (key2482, 1), (key2472, 1), (key2543, 1), (key2538, 1), (key2506, 2), (key2503, 2), (key2554, 2), (key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2440, -1), (key2437, -1), (key2522, -1), (key2503, -1), (key2563, -1), (key2554, -1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1)]

def rawRow2971 : Integer.Sparse Key := [(key2480, -2), (key2543, -2), (key2482, -2), (key2472, 1), (key2538, 1), (key2406, 1), (key2543, 1), (key2409, 1), (key2482, 1), (key2503, 2), (key2554, 2), (key2506, 2), (key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2503, -1), (key2554, -1), (key2437, -1), (key2563, -1), (key2440, -1), (key2522, -1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1)]

def rawRow2972 : Integer.Sparse Key := [(key2543, -2), (key2480, -2), (key2482, -2), (key2538, 1), (key2472, 1), (key2543, 1), (key2406, 1), (key2482, 1), (key2409, 1), (key2554, 2), (key2503, 2), (key2506, 2), (key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2554, -1), (key2503, -1), (key2563, -1), (key2437, -1), (key2522, -1), (key2440, -1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1)]

def rawRow2973 : Integer.Sparse Key := [(key2482, -2), (key2543, -2), (key2480, -2), (key2482, 1), (key2543, 1), (key2409, 1), (key2538, 1), (key2406, 1), (key2472, 1), (key2506, 2), (key2554, 2), (key2503, 2), (key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2522, -1), (key2563, -1), (key2440, -1), (key2554, -1), (key2437, -1), (key2503, -1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1)]

def rawRow2974 : Integer.Sparse Key := [(key2543, -2), (key2482, -2), (key2480, -2), (key2543, 1), (key2482, 1), (key2538, 1), (key2409, 1), (key2472, 1), (key2406, 1), (key2554, 2), (key2506, 2), (key2503, 2), (key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2563, -1), (key2522, -1), (key2554, -1), (key2440, -1), (key2503, -1), (key2437, -1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1)]

def rawRow2975 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2440, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2390, 2), (key2392, 2), (key2392, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2378, -1), (key2381, -1), (key2378, -1), (key2392, -1), (key2381, -1), (key2392, -1), (key2406, 1), (key2409, 1), (key2406, 1), (key2440, 1), (key2409, 1), (key2440, 1)]

def rawRow2976 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2440, -2), (key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2392, 2), (key2390, 2), (key2392, 2), (key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2381, -1), (key2378, -1), (key2392, -1), (key2378, -1), (key2392, -1), (key2381, -1), (key2409, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2409, 1)]

def rawRow2977 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2437, -2), (key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2392, 2), (key2392, 2), (key2390, 2), (key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2392, -1), (key2392, -1), (key2381, -1), (key2381, -1), (key2378, -1), (key2378, -1), (key2440, 1), (key2440, 1), (key2409, 1), (key2409, 1), (key2406, 1), (key2406, 1)]

def rawRow2978 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2554, -2), (key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2480, 2), (key2482, 2), (key2543, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2406, -1), (key2409, -1), (key2472, -1), (key2482, -1), (key2538, -1), (key2543, -1), (key2378, 1), (key2381, 1), (key2472, 1), (key2506, 1), (key2538, 1), (key2554, 1)]

def rawRow2979 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2554, -2), (key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2482, 2), (key2480, 2), (key2543, 2), (key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2409, -1), (key2406, -1), (key2482, -1), (key2472, -1), (key2543, -1), (key2538, -1), (key2381, 1), (key2378, 1), (key2506, 1), (key2472, 1), (key2554, 1), (key2538, 1)]

def rawRow2980 : Integer.Sparse Key := [(key2503, -2), (key2554, -2), (key2506, -2), (key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 2), (key2543, 2), (key2482, 2), (key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2472, -1), (key2538, -1), (key2406, -1), (key2543, -1), (key2409, -1), (key2482, -1), (key2472, 1), (key2538, 1), (key2378, 1), (key2554, 1), (key2381, 1), (key2506, 1)]

def rawRow2981 : Integer.Sparse Key := [(key2554, -2), (key2503, -2), (key2506, -2), (key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 2), (key2480, 2), (key2482, 2), (key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2538, -1), (key2472, -1), (key2543, -1), (key2406, -1), (key2482, -1), (key2409, -1), (key2538, 1), (key2472, 1), (key2554, 1), (key2378, 1), (key2506, 1), (key2381, 1)]

def rawRow2982 : Integer.Sparse Key := [(key2506, -2), (key2554, -2), (key2503, -2), (key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2482, 2), (key2543, 2), (key2480, 2), (key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2482, -1), (key2543, -1), (key2409, -1), (key2538, -1), (key2406, -1), (key2472, -1), (key2506, 1), (key2554, 1), (key2381, 1), (key2538, 1), (key2378, 1), (key2472, 1)]

def rawRow2983 : Integer.Sparse Key := [(key2554, -2), (key2506, -2), (key2503, -2), (key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2543, 2), (key2482, 2), (key2480, 2), (key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2543, -1), (key2482, -1), (key2538, -1), (key2409, -1), (key2472, -1), (key2406, -1), (key2554, 1), (key2506, 1), (key2538, 1), (key2381, 1), (key2472, 1), (key2378, 1)]

def rawRow3032 : Integer.Sparse Key := [(key2621, -2), (key2835, -2), (key2835, -2), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2641, 2), (key2976, 2), (key2976, 2), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2653, -1), (key2653, -1), (key2897, -1), (key2897, -1), (key2998, -1), (key2998, -1), (key2648, 1), (key2648, 1), (key2737, 1), (key2737, 1), (key2997, 1), (key2997, 1)]

def rawRow3033 : Integer.Sparse Key := [(key2835, -2), (key2621, -2), (key2835, -2), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2976, 2), (key2641, 2), (key2976, 2), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2897, -1), (key2998, -1), (key2653, -1), (key2998, -1), (key2653, -1), (key2897, -1), (key2737, 1), (key2997, 1), (key2648, 1), (key2997, 1), (key2648, 1), (key2737, 1)]

def rawRow3034 : Integer.Sparse Key := [(key2835, -2), (key2835, -2), (key2621, -2), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2616, 1), (key2976, 2), (key2976, 2), (key2641, 2), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2628, -1), (key2998, -1), (key2897, -1), (key2998, -1), (key2653, -1), (key2897, -1), (key2653, -1), (key2997, 1), (key2737, 1), (key2997, 1), (key2648, 1), (key2737, 1), (key2648, 1)]

def rawRow3035 : Integer.Sparse Key := [(key2644, -2), (key2732, -2), (key2885, -2), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, 1), (key2870, 1), (key2660, 2), (key2758, 2), (key2927, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2641, -1), (key2653, -1), (key2795, -1), (key2897, -1), (key2943, -1), (key2976, -1), (key2618, 1), (key2648, 1), (key2673, 1), (key2737, 1), (key2938, 1), (key2950, 1)]

def rawRow3036 : Integer.Sparse Key := [(key2644, -2), (key2885, -2), (key2732, -2), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2726, 1), (key2660, 2), (key2927, 2), (key2758, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2653, -1), (key2641, -1), (key2897, -1), (key2795, -1), (key2976, -1), (key2943, -1), (key2648, 1), (key2618, 1), (key2737, 1), (key2673, 1), (key2950, 1), (key2938, 1)]

def rawRow3037 : Integer.Sparse Key := [(key2732, -2), (key2644, -2), (key2885, -2), (key2706, 1), (key2726, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2758, 2), (key2660, 2), (key2927, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2795, -1), (key2943, -1), (key2641, -1), (key2976, -1), (key2653, -1), (key2897, -1), (key2673, 1), (key2938, 1), (key2618, 1), (key2950, 1), (key2648, 1), (key2737, 1)]

def rawRow3038 : Integer.Sparse Key := [(key2732, -2), (key2885, -2), (key2644, -2), (key2726, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2860, 1), (key2640, 1), (key2758, 2), (key2927, 2), (key2660, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2943, -1), (key2795, -1), (key2976, -1), (key2641, -1), (key2897, -1), (key2653, -1), (key2938, 1), (key2673, 1), (key2950, 1), (key2618, 1), (key2737, 1), (key2648, 1)]

def rawRow3039 : Integer.Sparse Key := [(key2885, -2), (key2644, -2), (key2732, -2), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, 1), (key2706, 1), (key2927, 2), (key2660, 2), (key2758, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2897, -1), (key2976, -1), (key2653, -1), (key2943, -1), (key2641, -1), (key2795, -1), (key2737, 1), (key2950, 1), (key2648, 1), (key2938, 1), (key2618, 1), (key2673, 1)]

def rawRow3040 : Integer.Sparse Key := [(key2885, -2), (key2732, -2), (key2644, -2), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2927, 2), (key2758, 2), (key2660, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2976, -1), (key2897, -1), (key2943, -1), (key2653, -1), (key2795, -1), (key2641, -1), (key2950, 1), (key2737, 1), (key2938, 1), (key2648, 1), (key2673, 1), (key2618, 1)]

def rawRow3041 : Integer.Sparse Key := [(key2658, -2), (key2923, -2), (key2923, -2), (key2660, 1), (key2660, 1), (key2920, 1), (key2920, 1), (key2927, 1), (key2927, 1), (key2621, 2), (key2835, 2), (key2835, 2), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, -1), (key2885, -1), (key2616, -1), (key2616, -1), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3042 : Integer.Sparse Key := [(key2923, -2), (key2658, -2), (key2923, -2), (key2920, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2920, 1), (key2835, 2), (key2621, 2), (key2835, 2), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3043 : Integer.Sparse Key := [(key2923, -2), (key2923, -2), (key2658, -2), (key2927, 1), (key2920, 1), (key2927, 1), (key2660, 1), (key2920, 1), (key2660, 1), (key2835, 2), (key2835, 2), (key2621, 2), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2644, -1), (key2829, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2616, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3044 : Integer.Sparse Key := [(key2660, -2), (key2758, -2), (key2927, -2), (key2658, 1), (key2660, 1), (key2753, 1), (key2920, 1), (key2758, 1), (key2923, 1), (key2644, 2), (key2732, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2860, -1), (key2726, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow3045 : Integer.Sparse Key := [(key2660, -2), (key2927, -2), (key2758, -2), (key2660, 1), (key2658, 1), (key2920, 1), (key2753, 1), (key2923, 1), (key2758, 1), (key2644, 2), (key2885, 2), (key2732, 2), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2732, -1), (key2640, -1), (key2632, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2726, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow3046 : Integer.Sparse Key := [(key2758, -2), (key2660, -2), (key2927, -2), (key2753, 1), (key2758, 1), (key2658, 1), (key2923, 1), (key2660, 1), (key2920, 1), (key2732, 2), (key2644, 2), (key2885, 2), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2706, -1), (key2726, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow3047 : Integer.Sparse Key := [(key2758, -2), (key2927, -2), (key2660, -2), (key2758, 1), (key2753, 1), (key2923, 1), (key2658, 1), (key2920, 1), (key2660, 1), (key2732, 2), (key2885, 2), (key2644, 2), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, -1), (key2644, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2860, -1), (key2640, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow3048 : Integer.Sparse Key := [(key2927, -2), (key2660, -2), (key2758, -2), (key2920, 1), (key2923, 1), (key2660, 1), (key2758, 1), (key2658, 1), (key2753, 1), (key2885, 2), (key2644, 2), (key2732, 2), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, -1), (key2676, -1), (key2860, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2632, -1), (key2706, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow3049 : Integer.Sparse Key := [(key2927, -2), (key2758, -2), (key2660, -2), (key2923, 1), (key2920, 1), (key2758, 1), (key2660, 1), (key2753, 1), (key2658, 1), (key2885, 2), (key2732, 2), (key2644, 2), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, -1), (key2621, -1), (key2870, -1), (key2860, -1), (key2726, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow3068 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2724, 1), (key2724, 1), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1)]

def rawRow3069 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2704, 1), (key2724, 1), (key2669, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1)]

def rawRow3070 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2724, 1), (key2704, 1), (key2724, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1)]

def rawRow3071 : Integer.Sparse Key := [(key2918, -2), (key2919, -2), (key2922, -2), (key2784, 1), (key2792, 1), (key2807, 1), (key2858, 1), (key2827, 1), (key2868, 1), (key3021, 2), (key3022, 2), (key3025, 2), (key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3022, -1), (key3016, -1), (key3025, -1), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3072 : Integer.Sparse Key := [(key2919, -2), (key2918, -2), (key2922, -2), (key2792, 1), (key2784, 1), (key2858, 1), (key2807, 1), (key2868, 1), (key2827, 1), (key3022, 2), (key3021, 2), (key3025, 2), (key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key3009, -1), (key3007, -1), (key3022, -1), (key3011, -1), (key3025, -1), (key3016, -1), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1)]

def rawRow3073 : Integer.Sparse Key := [(key2918, -2), (key2922, -2), (key2919, -2), (key2807, 1), (key2827, 1), (key2784, 1), (key2868, 1), (key2792, 1), (key2858, 1), (key3021, 2), (key3025, 2), (key3022, 2), (key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key3011, -1), (key3016, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1)]

def rawRow3074 : Integer.Sparse Key := [(key2922, -2), (key2918, -2), (key2919, -2), (key2827, 1), (key2807, 1), (key2868, 1), (key2784, 1), (key2858, 1), (key2792, 1), (key3025, 2), (key3021, 2), (key3022, 2), (key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3022, -1), (key3009, -1), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1)]

def rawRow3075 : Integer.Sparse Key := [(key2919, -2), (key2922, -2), (key2918, -2), (key2858, 1), (key2868, 1), (key2792, 1), (key2827, 1), (key2784, 1), (key2807, 1), (key3022, 2), (key3025, 2), (key3021, 2), (key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key3022, -1), (key3025, -1), (key3009, -1), (key3016, -1), (key3007, -1), (key3011, -1), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1)]

def rawRow3076 : Integer.Sparse Key := [(key2922, -2), (key2919, -2), (key2918, -2), (key2868, 1), (key2858, 1), (key2827, 1), (key2792, 1), (key2807, 1), (key2784, 1), (key3025, 2), (key3022, 2), (key3021, 2), (key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key3025, -1), (key3022, -1), (key3016, -1), (key3009, -1), (key3011, -1), (key3007, -1), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

def rawRow3077 : Integer.Sparse Key := [(key3011, -2), (key3011, -2), (key3016, -2), (key3007, 1), (key3007, 1), (key3021, 1), (key3021, 1), (key3025, 1), (key3025, 1), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1)]

def rawRow3078 : Integer.Sparse Key := [(key3011, -2), (key3016, -2), (key3011, -2), (key3021, 1), (key3025, 1), (key3007, 1), (key3025, 1), (key3007, 1), (key3021, 1), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1)]

def rawRow3079 : Integer.Sparse Key := [(key3016, -2), (key3011, -2), (key3011, -2), (key3025, 1), (key3021, 1), (key3025, 1), (key3007, 1), (key3021, 1), (key3007, 1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1)]

def rawRow3080 : Integer.Sparse Key := [(key3021, -2), (key3022, -2), (key3025, -2), (key3007, 1), (key3009, 1), (key3011, 1), (key3022, 1), (key3016, 1), (key3025, 1), (key2918, 2), (key2919, 2), (key2922, 2), (key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2858, -1), (key2827, -1), (key2868, -1), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1)]

def rawRow3081 : Integer.Sparse Key := [(key3022, -2), (key3021, -2), (key3025, -2), (key3009, 1), (key3007, 1), (key3022, 1), (key3011, 1), (key3025, 1), (key3016, 1), (key2919, 2), (key2918, 2), (key2922, 2), (key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2792, -1), (key2784, -1), (key2858, -1), (key2807, -1), (key2868, -1), (key2827, -1), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1)]

def rawRow3082 : Integer.Sparse Key := [(key3021, -2), (key3025, -2), (key3022, -2), (key3011, 1), (key3016, 1), (key3007, 1), (key3025, 1), (key3009, 1), (key3022, 1), (key2918, 2), (key2922, 2), (key2919, 2), (key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2807, -1), (key2827, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1)]

def rawRow3083 : Integer.Sparse Key := [(key3025, -2), (key3021, -2), (key3022, -2), (key3016, 1), (key3011, 1), (key3025, 1), (key3007, 1), (key3022, 1), (key3009, 1), (key2922, 2), (key2918, 2), (key2919, 2), (key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2858, -1), (key2792, -1), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1)]

def rawRow3084 : Integer.Sparse Key := [(key3022, -2), (key3025, -2), (key3021, -2), (key3022, 1), (key3025, 1), (key3009, 1), (key3016, 1), (key3007, 1), (key3011, 1), (key2919, 2), (key2922, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2858, -1), (key2868, -1), (key2792, -1), (key2827, -1), (key2784, -1), (key2807, -1), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1)]

def rawRow3085 : Integer.Sparse Key := [(key3025, -2), (key3022, -2), (key3021, -2), (key3025, 1), (key3022, 1), (key3016, 1), (key3009, 1), (key3011, 1), (key3007, 1), (key2922, 2), (key2919, 2), (key2918, 2), (key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2868, -1), (key2858, -1), (key2827, -1), (key2792, -1), (key2807, -1), (key2784, -1), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

def rawRow3152 : Integer.Sparse Key := [(key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1594, -1), (key1594, -1), (key1291, 2), (key1568, 2), (key1568, 2), (key1352, 1), (key1352, 1), (key1682, 1), (key1682, 1), (key1690, 1), (key1690, 1), (key1311, -1), (key1311, -1), (key1541, -1), (key1541, -1), (key1617, -1), (key1617, -1), (key1355, -2), (key1684, -2), (key1684, -2), (key1327, 1), (key1327, 1), (key1557, 1), (key1557, 1), (key1625, 1), (key1625, 1)]

def rawRow3153 : Integer.Sparse Key := [(key1576, -1), (key1594, -1), (key1299, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1568, 2), (key1291, 2), (key1568, 2), (key1682, 1), (key1690, 1), (key1352, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1541, -1), (key1617, -1), (key1311, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1684, -2), (key1355, -2), (key1684, -2), (key1557, 1), (key1625, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1557, 1)]

def rawRow3154 : Integer.Sparse Key := [(key1594, -1), (key1576, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1568, 2), (key1568, 2), (key1291, 2), (key1690, 1), (key1682, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1352, 1), (key1617, -1), (key1541, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1311, -1), (key1684, -2), (key1684, -2), (key1355, -2), (key1625, 1), (key1557, 1), (key1625, 1), (key1327, 1), (key1557, 1), (key1327, 1)]

def rawRow3167 : Integer.Sparse Key := [(key1352, -1), (key1352, -1), (key1682, -1), (key1682, -1), (key1690, -1), (key1690, -1), (key1355, 2), (key1684, 2), (key1684, 2), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1), (key1327, -1), (key1327, -1), (key1557, -1), (key1557, -1), (key1625, -1), (key1625, -1), (key1291, -2), (key1568, -2), (key1568, -2), (key1311, 1), (key1311, 1), (key1541, 1), (key1541, 1), (key1617, 1), (key1617, 1)]

def rawRow3168 : Integer.Sparse Key := [(key1682, -1), (key1690, -1), (key1352, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1684, 2), (key1355, 2), (key1684, 2), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1557, -1), (key1625, -1), (key1327, -1), (key1625, -1), (key1327, -1), (key1557, -1), (key1568, -2), (key1291, -2), (key1568, -2), (key1541, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1541, 1)]

def rawRow3169 : Integer.Sparse Key := [(key1690, -1), (key1682, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1352, -1), (key1684, 2), (key1684, 2), (key1355, 2), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1), (key1625, -1), (key1557, -1), (key1625, -1), (key1327, -1), (key1557, -1), (key1327, -1), (key1568, -2), (key1568, -2), (key1291, -2), (key1617, 1), (key1541, 1), (key1617, 1), (key1311, 1), (key1541, 1), (key1311, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3212 : Integer.Sparse Key := [(key1473, -2), (key1473, -2), (key1481, -2), (key1394, 1), (key1394, 1), (key1427, 1), (key1427, 1), (key1445, 1), (key1445, 1), (key1904, 2), (key1904, 2), (key1912, 2), (key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1594, -1), (key1594, -1), (key1897, -1), (key1897, -1), (key1919, -1), (key1919, -1), (key1927, -1), (key1927, -1), (key1352, 1), (key1352, 1), (key1682, 1), (key1682, 1), (key1690, 1), (key1690, 1)]

def rawRow3213 : Integer.Sparse Key := [(key1473, -2), (key1481, -2), (key1473, -2), (key1427, 1), (key1445, 1), (key1394, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1904, 2), (key1912, 2), (key1904, 2), (key1576, -1), (key1594, -1), (key1299, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1919, -1), (key1927, -1), (key1897, -1), (key1927, -1), (key1897, -1), (key1919, -1), (key1682, 1), (key1690, 1), (key1352, 1), (key1690, 1), (key1352, 1), (key1682, 1)]

def rawRow3214 : Integer.Sparse Key := [(key1481, -2), (key1473, -2), (key1473, -2), (key1445, 1), (key1427, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1394, 1), (key1912, 2), (key1904, 2), (key1904, 2), (key1594, -1), (key1576, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1927, -1), (key1919, -1), (key1927, -1), (key1897, -1), (key1919, -1), (key1897, -1), (key1690, 1), (key1682, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1352, 1)]

def rawRow3227 : Integer.Sparse Key := [(key1904, -2), (key1904, -2), (key1912, -2), (key1897, 1), (key1897, 1), (key1919, 1), (key1919, 1), (key1927, 1), (key1927, 1), (key1473, 2), (key1473, 2), (key1481, 2), (key1352, -1), (key1352, -1), (key1682, -1), (key1682, -1), (key1690, -1), (key1690, -1), (key1394, -1), (key1394, -1), (key1427, -1), (key1427, -1), (key1445, -1), (key1445, -1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1)]

def rawRow3228 : Integer.Sparse Key := [(key1904, -2), (key1912, -2), (key1904, -2), (key1919, 1), (key1927, 1), (key1897, 1), (key1927, 1), (key1897, 1), (key1919, 1), (key1473, 2), (key1481, 2), (key1473, 2), (key1682, -1), (key1690, -1), (key1352, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1427, -1), (key1445, -1), (key1394, -1), (key1445, -1), (key1394, -1), (key1427, -1), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1)]

def rawRow3229 : Integer.Sparse Key := [(key1912, -2), (key1904, -2), (key1904, -2), (key1927, 1), (key1919, 1), (key1927, 1), (key1897, 1), (key1919, 1), (key1897, 1), (key1481, 2), (key1473, 2), (key1473, 2), (key1690, -1), (key1682, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1352, -1), (key1445, -1), (key1427, -1), (key1445, -1), (key1394, -1), (key1427, -1), (key1394, -1), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1)]

def rawRow3266 : Integer.Sparse Key := [(key2671, -2), (key2726, -2), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, 1), (key2753, 1), (key2732, 1), (key2758, 1), (key2702, 2), (key2972, 2), (key2976, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2728, -1), (key2976, -1), (key2983, -1), (key2735, -1), (key2737, -1), (key2893, -1), (key2897, -1), (key2997, -1), (key2998, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2747, 1), (key2998, 1), (key3000, 1)]

def rawRow3267 : Integer.Sparse Key := [(key2671, -2), (key2758, -2), (key2726, -2), (key2676, 1), (key2671, 1), (key2753, 1), (key2706, 1), (key2758, 1), (key2732, 1), (key2702, 2), (key2976, 2), (key2972, 2), (key2641, -1), (key2628, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2976, -1), (key2737, -1), (key2735, -1), (key2897, -1), (key2893, -1), (key2998, -1), (key2997, -1), (key2653, 1), (key2646, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2998, 1)]

def rawRow3268 : Integer.Sparse Key := [(key2726, -2), (key2671, -2), (key2758, -2), (key2706, 1), (key2732, 1), (key2671, 1), (key2758, 1), (key2676, 1), (key2753, 1), (key2972, 2), (key2702, 2), (key2976, 2), (key2702, -1), (key2976, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2893, -1), (key2997, -1), (key2735, -1), (key2998, -1), (key2737, -1), (key2897, -1), (key2735, 1), (key2998, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2747, 1)]

def rawRow3269 : Integer.Sparse Key := [(key2726, -2), (key2758, -2), (key2671, -2), (key2732, 1), (key2706, 1), (key2758, 1), (key2671, 1), (key2753, 1), (key2676, 1), (key2972, 2), (key2976, 2), (key2702, 2), (key2976, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2728, -1), (key2641, -1), (key2997, -1), (key2893, -1), (key2998, -1), (key2735, -1), (key2897, -1), (key2737, -1), (key2998, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2747, 1), (key2653, 1)]

def rawRow3270 : Integer.Sparse Key := [(key2758, -2), (key2671, -2), (key2726, -2), (key2753, 1), (key2758, 1), (key2676, 1), (key2732, 1), (key2671, 1), (key2706, 1), (key2976, 2), (key2702, 2), (key2972, 2), (key2728, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2628, -1), (key2702, -1), (key2897, -1), (key2998, -1), (key2737, -1), (key2997, -1), (key2735, -1), (key2893, -1), (key2747, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2646, 1), (key2735, 1)]

def rawRow3271 : Integer.Sparse Key := [(key2758, -2), (key2726, -2), (key2671, -2), (key2758, 1), (key2753, 1), (key2732, 1), (key2676, 1), (key2706, 1), (key2671, 1), (key2976, 2), (key2972, 2), (key2702, 2), (key2983, -1), (key2728, -1), (key2976, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2998, -1), (key2897, -1), (key2997, -1), (key2737, -1), (key2893, -1), (key2735, -1), (key3000, 1), (key2747, 1), (key2998, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

def rawRow3272 : Integer.Sparse Key := [(key2676, -2), (key2732, -2), (key2732, -2), (key2671, 1), (key2671, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2728, 2), (key2983, 2), (key2983, 2), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2747, -1), (key2747, -1), (key2904, -1), (key2904, -1), (key3000, -1), (key3000, -1), (key2648, 1), (key2648, 1), (key2737, 1), (key2737, 1), (key2997, 1), (key2997, 1)]

def rawRow3273 : Integer.Sparse Key := [(key2732, -2), (key2676, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2983, 2), (key2728, 2), (key2983, 2), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2904, -1), (key3000, -1), (key2747, -1), (key3000, -1), (key2747, -1), (key2904, -1), (key2737, 1), (key2997, 1), (key2648, 1), (key2997, 1), (key2648, 1), (key2737, 1)]

def rawRow3274 : Integer.Sparse Key := [(key2732, -2), (key2732, -2), (key2676, -2), (key2726, 1), (key2706, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2671, 1), (key2983, 2), (key2983, 2), (key2728, 2), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2904, -1), (key3000, -1), (key2747, -1), (key2904, -1), (key2747, -1), (key2997, 1), (key2737, 1), (key2997, 1), (key2648, 1), (key2737, 1), (key2648, 1)]

def rawRow3275 : Integer.Sparse Key := [(key2786, -2), (key2870, -2), (key2923, -2), (key2794, 1), (key2798, 1), (key2860, 1), (key2920, 1), (key2885, 1), (key2927, 1), (key2671, 2), (key2726, 2), (key2758, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2747, -1), (key2998, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2782, -1), (key2795, -1), (key2938, -1), (key2943, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2728, 1), (key2976, 1), (key2983, 1)]

def rawRow3276 : Integer.Sparse Key := [(key2786, -2), (key2923, -2), (key2870, -2), (key2798, 1), (key2794, 1), (key2920, 1), (key2860, 1), (key2927, 1), (key2885, 1), (key2671, 2), (key2758, 2), (key2726, 2), (key2653, -1), (key2646, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2998, -1), (key2673, -1), (key2667, -1), (key2795, -1), (key2782, -1), (key2943, -1), (key2938, -1), (key2641, 1), (key2628, 1), (key2728, 1), (key2702, 1), (key2983, 1), (key2976, 1)]

def rawRow3277 : Integer.Sparse Key := [(key2870, -2), (key2786, -2), (key2923, -2), (key2860, 1), (key2885, 1), (key2794, 1), (key2927, 1), (key2798, 1), (key2920, 1), (key2726, 2), (key2671, 2), (key2758, 2), (key2735, -1), (key2998, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2782, -1), (key2938, -1), (key2667, -1), (key2943, -1), (key2673, -1), (key2795, -1), (key2702, 1), (key2976, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2728, 1)]

def rawRow3278 : Integer.Sparse Key := [(key2870, -2), (key2923, -2), (key2786, -2), (key2885, 1), (key2860, 1), (key2927, 1), (key2794, 1), (key2920, 1), (key2798, 1), (key2726, 2), (key2758, 2), (key2671, 2), (key2998, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2747, -1), (key2653, -1), (key2938, -1), (key2782, -1), (key2943, -1), (key2667, -1), (key2795, -1), (key2673, -1), (key2976, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2728, 1), (key2641, 1)]

def rawRow3279 : Integer.Sparse Key := [(key2923, -2), (key2786, -2), (key2870, -2), (key2920, 1), (key2927, 1), (key2798, 1), (key2885, 1), (key2794, 1), (key2860, 1), (key2758, 2), (key2671, 2), (key2726, 2), (key2747, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2646, -1), (key2735, -1), (key2795, -1), (key2943, -1), (key2673, -1), (key2938, -1), (key2667, -1), (key2782, -1), (key2728, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2628, 1), (key2702, 1)]

def rawRow3280 : Integer.Sparse Key := [(key2923, -2), (key2870, -2), (key2786, -2), (key2927, 1), (key2920, 1), (key2885, 1), (key2798, 1), (key2860, 1), (key2794, 1), (key2758, 2), (key2726, 2), (key2671, 2), (key3000, -1), (key2747, -1), (key2998, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2943, -1), (key2795, -1), (key2938, -1), (key2673, -1), (key2782, -1), (key2667, -1), (key2983, 1), (key2728, 1), (key2976, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

def rawRow3281 : Integer.Sparse Key := [(key2798, -2), (key2835, -2), (key2885, -2), (key2786, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2829, 1), (key2870, 1), (key3010, 2), (key3017, 2), (key3030, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2728, -1), (key2747, -1), (key2831, -1), (key2904, -1), (key2960, -1), (key2983, -1), (key2618, 1), (key2648, 1), (key2673, 1), (key2737, 1), (key2938, 1), (key2950, 1)]

def rawRow3282 : Integer.Sparse Key := [(key2798, -2), (key2885, -2), (key2835, -2), (key2794, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, 1), (key2829, 1), (key3010, 2), (key3030, 2), (key3017, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2747, -1), (key2728, -1), (key2904, -1), (key2831, -1), (key2983, -1), (key2960, -1), (key2648, 1), (key2618, 1), (key2737, 1), (key2673, 1), (key2950, 1), (key2938, 1)]

def rawRow3283 : Integer.Sparse Key := [(key2835, -2), (key2798, -2), (key2885, -2), (key2809, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2794, 1), (key2860, 1), (key3017, 2), (key3010, 2), (key3030, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2831, -1), (key2960, -1), (key2728, -1), (key2983, -1), (key2747, -1), (key2904, -1), (key2673, 1), (key2938, 1), (key2618, 1), (key2950, 1), (key2648, 1), (key2737, 1)]

def rawRow3284 : Integer.Sparse Key := [(key2835, -2), (key2885, -2), (key2798, -2), (key2829, 1), (key2809, 1), (key2870, 1), (key2786, 1), (key2860, 1), (key2794, 1), (key3017, 2), (key3030, 2), (key3010, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2960, -1), (key2831, -1), (key2983, -1), (key2728, -1), (key2904, -1), (key2747, -1), (key2938, 1), (key2673, 1), (key2950, 1), (key2618, 1), (key2737, 1), (key2648, 1)]

def rawRow3285 : Integer.Sparse Key := [(key2885, -2), (key2798, -2), (key2835, -2), (key2860, 1), (key2870, 1), (key2794, 1), (key2829, 1), (key2786, 1), (key2809, 1), (key3030, 2), (key3010, 2), (key3017, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2904, -1), (key2983, -1), (key2747, -1), (key2960, -1), (key2728, -1), (key2831, -1), (key2737, 1), (key2950, 1), (key2648, 1), (key2938, 1), (key2618, 1), (key2673, 1)]

def rawRow3286 : Integer.Sparse Key := [(key2885, -2), (key2835, -2), (key2798, -2), (key2870, 1), (key2860, 1), (key2829, 1), (key2794, 1), (key2809, 1), (key2786, 1), (key3030, 2), (key3017, 2), (key3010, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2983, -1), (key2904, -1), (key2960, -1), (key2747, -1), (key2831, -1), (key2728, -1), (key2950, 1), (key2737, 1), (key2938, 1), (key2648, 1), (key2673, 1), (key2618, 1)]

def rawRow3287 : Integer.Sparse Key := [(key3008, -2), (key3026, -2), (key3026, -2), (key3010, 1), (key3010, 1), (key3023, 1), (key3023, 1), (key3030, 1), (key3030, 1), (key2676, 2), (key2732, 2), (key2732, 2), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, -1), (key2885, -1), (key2671, -1), (key2671, -1), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3288 : Integer.Sparse Key := [(key3026, -2), (key3008, -2), (key3026, -2), (key3023, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3023, 1), (key2732, 2), (key2676, 2), (key2732, 2), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3289 : Integer.Sparse Key := [(key3026, -2), (key3026, -2), (key3008, -2), (key3030, 1), (key3023, 1), (key3030, 1), (key3010, 1), (key3023, 1), (key3010, 1), (key2732, 2), (key2732, 2), (key2676, 2), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2644, -1), (key2726, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2671, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3290 : Integer.Sparse Key := [(key3010, -2), (key3017, -2), (key3030, -2), (key3008, 1), (key3010, 1), (key3012, 1), (key3023, 1), (key3017, 1), (key3026, 1), (key2798, 2), (key2835, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2860, -1), (key2829, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow3291 : Integer.Sparse Key := [(key3010, -2), (key3030, -2), (key3017, -2), (key3010, 1), (key3008, 1), (key3023, 1), (key3012, 1), (key3026, 1), (key3017, 1), (key2798, 2), (key2885, 2), (key2835, 2), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2732, -1), (key2794, -1), (key2786, -1), (key2860, -1), (key2809, -1), (key2870, -1), (key2829, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow3292 : Integer.Sparse Key := [(key3017, -2), (key3010, -2), (key3030, -2), (key3012, 1), (key3017, 1), (key3008, 1), (key3026, 1), (key3010, 1), (key3023, 1), (key2835, 2), (key2798, 2), (key2885, 2), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2809, -1), (key2829, -1), (key2786, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow3293 : Integer.Sparse Key := [(key3017, -2), (key3030, -2), (key3010, -2), (key3017, 1), (key3012, 1), (key3026, 1), (key3008, 1), (key3023, 1), (key3010, 1), (key2835, 2), (key2885, 2), (key2798, 2), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, -1), (key2644, -1), (key2829, -1), (key2809, -1), (key2870, -1), (key2786, -1), (key2860, -1), (key2794, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow3294 : Integer.Sparse Key := [(key3030, -2), (key3010, -2), (key3017, -2), (key3023, 1), (key3026, 1), (key3010, 1), (key3017, 1), (key3008, 1), (key3012, 1), (key2885, 2), (key2798, 2), (key2835, 2), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, -1), (key2676, -1), (key2860, -1), (key2870, -1), (key2794, -1), (key2829, -1), (key2786, -1), (key2809, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow3295 : Integer.Sparse Key := [(key3030, -2), (key3017, -2), (key3010, -2), (key3026, 1), (key3023, 1), (key3017, 1), (key3010, 1), (key3012, 1), (key3008, 1), (key2885, 2), (key2835, 2), (key2798, 2), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, -1), (key2621, -1), (key2870, -1), (key2860, -1), (key2829, -1), (key2794, -1), (key2809, -1), (key2786, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow3302 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2435, -2), (key2398, 6), (key2876, 2), (key2876, 2), (key3028, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2925, -6), (key2604, 2), (key2916, 2), (key2916, 2)]

def rawRow3303 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2404, -2), (key2398, 6), (key2876, 2), (key3028, 2), (key2876, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2925, -6), (key2916, 2), (key2604, 2), (key2916, 2)]

def rawRow3304 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2404, -2), (key2398, 6), (key3028, 2), (key2876, 2), (key2876, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2925, -6), (key2916, 2), (key2916, 2), (key2604, 2)]

def rawRow3317 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2575, -2), (key2570, 6), (key2404, 2), (key2404, 2), (key2435, 2), (key2388, -2), (key2478, -2), (key2478, -2), (key2398, -6), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow3318 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2568, -2), (key2570, 6), (key2404, 2), (key2435, 2), (key2404, 2), (key2478, -2), (key2388, -2), (key2478, -2), (key2398, -6), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow3319 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2568, -2), (key2570, 6), (key2435, 2), (key2404, 2), (key2404, 2), (key2478, -2), (key2478, -2), (key2388, -2), (key2398, -6), (key2839, 2), (key2839, 2), (key2583, 2)]

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

def rawRow262 : Integer.Sparse Key := [(key308, -1), (key308, -1), (key310, 2), (key391, 1), (key391, 1), (key402, -1), (key402, -1), (key570, -2), (key575, 1), (key575, 1), (key242, 1), (key242, 1), (key244, -2), (key412, -1), (key412, -1), (key423, 1), (key423, 1), (key580, 2), (key586, -1), (key586, -1), (key254, -1), (key254, -1), (key265, 1), (key265, 1), (key322, 1), (key322, 1), (key333, -1), (key333, -1), (key598, -1), (key598, -1), (key604, 1), (key604, 1), (key269, 2), (key274, -1), (key274, -1), (key337, -2), (key343, 1), (key343, 1), (key472, 1), (key472, 1), (key478, -1), (key478, -1)]

def rawRow265 : Integer.Sparse Key := [(key391, -1), (key391, -1), (key570, 2), (key308, 1), (key308, 1), (key575, -1), (key575, -1), (key310, -2), (key402, 1), (key402, 1), (key412, 1), (key412, 1), (key580, -2), (key242, -1), (key242, -1), (key586, 1), (key586, 1), (key244, 2), (key423, -1), (key423, -1), (key322, -1), (key322, -1), (key598, 1), (key598, 1), (key254, 1), (key254, 1), (key604, -1), (key604, -1), (key265, -1), (key265, -1), (key333, 1), (key333, 1), (key337, 2), (key472, -1), (key472, -1), (key269, -2), (key478, 1), (key478, 1), (key274, 1), (key274, 1), (key343, -1), (key343, -1)]

def rawRow272 : Integer.Sparse Key := [(key322, -1), (key322, -1), (key337, 2), (key412, 1), (key412, 1), (key472, -1), (key472, -1), (key580, -2), (key598, 1), (key598, 1), (key254, 1), (key254, 1), (key269, -2), (key391, -1), (key391, -1), (key478, 1), (key478, 1), (key570, 2), (key604, -1), (key604, -1), (key242, -1), (key242, -1), (key274, 1), (key274, 1), (key308, 1), (key308, 1), (key343, -1), (key343, -1), (key575, -1), (key575, -1), (key586, 1), (key586, 1), (key244, 2), (key265, -1), (key265, -1), (key310, -2), (key333, 1), (key333, 1), (key402, 1), (key402, 1), (key423, -1), (key423, -1)]

def rawRow275 : Integer.Sparse Key := [(key412, -1), (key412, -1), (key580, 2), (key322, 1), (key322, 1), (key598, -1), (key598, -1), (key337, -2), (key472, 1), (key472, 1), (key391, 1), (key391, 1), (key570, -2), (key254, -1), (key254, -1), (key604, 1), (key604, 1), (key269, 2), (key478, -1), (key478, -1), (key308, -1), (key308, -1), (key575, 1), (key575, 1), (key242, 1), (key242, 1), (key586, -1), (key586, -1), (key274, -1), (key274, -1), (key343, 1), (key343, 1), (key310, 2), (key402, -1), (key402, -1), (key244, -2), (key423, 1), (key423, 1), (key265, 1), (key265, 1), (key333, -1), (key333, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3356 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2937, -2), (key2664, 1), (key2668, 1), (key2779, 1), (key2791, 1), (key2937, 1), (key2942, 1), (key2802, 2), (key2806, 2), (key2949, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2826, -1), (key2949, -1), (key2959, -1), (key2699, -1), (key2703, -1), (key2852, -1), (key2857, -1), (key2973, -1), (key2975, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2867, 1), (key2973, 1), (key2982, 1)]

def rawRow3357 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2937, -2), (key2668, 1), (key2664, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2937, 1), (key2806, 2), (key2802, 2), (key2949, 2), (key2613, -1), (key2609, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2949, -1), (key2703, -1), (key2699, -1), (key2857, -1), (key2852, -1), (key2975, -1), (key2973, -1), (key2629, 1), (key2625, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2973, 1)]

def rawRow3358 : Integer.Sparse Key := [(key2779, -2), (key2937, -2), (key2783, -2), (key2779, 1), (key2937, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2802, 2), (key2949, 2), (key2806, 2), (key2802, -1), (key2949, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2852, -1), (key2973, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2852, 1), (key2973, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2867, 1)]

def rawRow3359 : Integer.Sparse Key := [(key2937, -2), (key2779, -2), (key2783, -2), (key2937, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2791, 1), (key2668, 1), (key2949, 2), (key2802, 2), (key2806, 2), (key2949, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2826, -1), (key2613, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2857, -1), (key2703, -1), (key2973, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2867, 1), (key2629, 1)]

def rawRow3360 : Integer.Sparse Key := [(key2783, -2), (key2937, -2), (key2779, -2), (key2791, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2664, 1), (key2779, 1), (key2806, 2), (key2949, 2), (key2802, 2), (key2826, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2609, -1), (key2802, -1), (key2857, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2699, -1), (key2852, -1), (key2867, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2625, 1), (key2852, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3488 : Integer.Sparse Key := [(key1334, -6), (key1288, 2), (key1308, 2), (key1308, 2), (key1769, 6), (key1383, -2), (key1538, -2), (key1538, -2), (key1785, -2), (key1810, -2), (key1810, -2), (key1452, 2), (key1652, 2), (key1652, 2)]

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

def rawRow294 : Integer.Sparse Key := [(key1301, -2), (key1305, 1), (key1305, 1), (key1321, 2), (key1332, -1), (key1332, -1), (key1342, -1), (key1342, -1), (key1348, 1), (key1348, 1), (key1396, 2), (key1400, -1), (key1400, -1), (key1429, -2), (key1450, 1), (key1450, 1), (key1460, 1), (key1460, 1), (key1469, -1), (key1469, -1), (key1551, -2), (key1562, 1), (key1562, 1), (key1578, 2), (key1599, -1), (key1599, -1), (key1662, -1), (key1662, -1), (key1670, 1), (key1670, 1), (key1777, 1), (key1777, 1), (key1783, -1), (key1783, -1), (key1793, -1), (key1793, -1), (key1801, 1), (key1801, 1), (key1820, 1), (key1820, 1), (key1828, -1), (key1828, -1)]

def rawRow297 : Integer.Sparse Key := [(key1321, -2), (key1342, 1), (key1342, 1), (key1301, 2), (key1348, -1), (key1348, -1), (key1305, -1), (key1305, -1), (key1332, 1), (key1332, 1), (key1429, 2), (key1460, -1), (key1460, -1), (key1396, -2), (key1469, 1), (key1469, 1), (key1400, 1), (key1400, 1), (key1450, -1), (key1450, -1), (key1578, -2), (key1662, 1), (key1662, 1), (key1551, 2), (key1670, -1), (key1670, -1), (key1562, -1), (key1562, -1), (key1599, 1), (key1599, 1), (key1793, 1), (key1793, 1), (key1820, -1), (key1820, -1), (key1777, -1), (key1777, -1), (key1828, 1), (key1828, 1), (key1783, 1), (key1783, 1), (key1801, -1), (key1801, -1)]

def rawRow304 : Integer.Sparse Key := [(key1396, -2), (key1400, 1), (key1400, 1), (key1551, 2), (key1562, -1), (key1562, -1), (key1777, -1), (key1777, -1), (key1783, 1), (key1783, 1), (key1301, 2), (key1305, -1), (key1305, -1), (key1578, -2), (key1599, 1), (key1599, 1), (key1793, 1), (key1793, 1), (key1801, -1), (key1801, -1), (key1321, -2), (key1332, 1), (key1332, 1), (key1429, 2), (key1450, -1), (key1450, -1), (key1820, -1), (key1820, -1), (key1828, 1), (key1828, 1), (key1342, 1), (key1342, 1), (key1348, -1), (key1348, -1), (key1460, -1), (key1460, -1), (key1469, 1), (key1469, 1), (key1662, 1), (key1662, 1), (key1670, -1), (key1670, -1)]

def rawRow307 : Integer.Sparse Key := [(key1551, -2), (key1777, 1), (key1777, 1), (key1396, 2), (key1783, -1), (key1783, -1), (key1400, -1), (key1400, -1), (key1562, 1), (key1562, 1), (key1578, 2), (key1793, -1), (key1793, -1), (key1301, -2), (key1801, 1), (key1801, 1), (key1305, 1), (key1305, 1), (key1599, -1), (key1599, -1), (key1429, -2), (key1820, 1), (key1820, 1), (key1321, 2), (key1828, -1), (key1828, -1), (key1332, -1), (key1332, -1), (key1450, 1), (key1450, 1), (key1460, 1), (key1460, 1), (key1662, -1), (key1662, -1), (key1342, -1), (key1342, -1), (key1670, 1), (key1670, 1), (key1348, 1), (key1348, 1), (key1469, -1), (key1469, -1)]

def rawRow314 : Integer.Sparse Key := [(key1429, -2), (key1460, 1), (key1460, 1), (key1578, 2), (key1662, -1), (key1662, -1), (key1793, -1), (key1793, -1), (key1820, 1), (key1820, 1), (key1321, 2), (key1342, -1), (key1342, -1), (key1551, -2), (key1670, 1), (key1670, 1), (key1777, 1), (key1777, 1), (key1828, -1), (key1828, -1), (key1301, -2), (key1348, 1), (key1348, 1), (key1396, 2), (key1469, -1), (key1469, -1), (key1783, -1), (key1783, -1), (key1801, 1), (key1801, 1), (key1305, 1), (key1305, 1), (key1332, -1), (key1332, -1), (key1400, -1), (key1400, -1), (key1450, 1), (key1450, 1), (key1562, 1), (key1562, 1), (key1599, -1), (key1599, -1)]

def rawRow317 : Integer.Sparse Key := [(key1578, -2), (key1793, 1), (key1793, 1), (key1429, 2), (key1820, -1), (key1820, -1), (key1460, -1), (key1460, -1), (key1662, 1), (key1662, 1), (key1551, 2), (key1777, -1), (key1777, -1), (key1321, -2), (key1828, 1), (key1828, 1), (key1342, 1), (key1342, 1), (key1670, -1), (key1670, -1), (key1396, -2), (key1783, 1), (key1783, 1), (key1301, 2), (key1801, -1), (key1801, -1), (key1348, -1), (key1348, -1), (key1469, 1), (key1469, 1), (key1400, 1), (key1400, 1), (key1562, -1), (key1562, -1), (key1305, -1), (key1305, -1), (key1599, 1), (key1599, 1), (key1332, 1), (key1332, 1), (key1450, -1), (key1450, -1)]

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

def rawRow336 : Integer.Sparse Key := [(key1300, -1), (key1300, -1), (key1306, 2), (key1320, 1), (key1320, 1), (key1333, -1), (key1333, -1), (key1353, -2), (key1356, 1), (key1356, 1), (key1395, 1), (key1395, 1), (key1401, -2), (key1428, -1), (key1428, -1), (key1451, 1), (key1451, 1), (key1474, 2), (key1482, -1), (key1482, -1), (key1550, -1), (key1550, -1), (key1563, 1), (key1563, 1), (key1577, 1), (key1577, 1), (key1600, -1), (key1600, -1), (key1685, -1), (key1685, -1), (key1691, 1), (key1691, 1), (key1898, 2), (key1901, -1), (key1901, -1), (key1905, -2), (key1913, 1), (key1913, 1), (key1922, 1), (key1922, 1), (key1928, -1), (key1928, -1)]

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

def nodeValue1179 : Sparse Master := [(Sum.inr 1179, (1 / 1))]

def nodeValue1180 : Sparse Master := [(Sum.inr 1180, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


